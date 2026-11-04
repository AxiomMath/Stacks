module

public import StacksFrontier.AlgebraicGeometry.Surfaces.FormalNeighborhoodMultiplicative

/-!
# Germs at the image point as compatible functions on the thickenings

Let `f : X ⟶ Y` be a morphism of schemes and let `D` be an ideal sheaf on `X` whose support is
carried by `f` to a single point `y`. Every infinitesimal thickening
`Eₙ₊₁ = (D ^ (n + 1)).subscheme` then lies over every open neighbourhood of `y`, so a function
defined near `y` pulls back to a function on each thickening, compatibly with restriction. This
gives a ring map

`𝒪_{Y, y} ⟶ A = lim H⁰(Eₙ, 𝒪_{Eₙ})`

into the ring of compatible functions
`AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodRing D`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.stalkToΓ` — for a morphism `h : T ⟶ Y` all of whose points go to
  `y`, the ring map `𝒪_{Y, y} ⟶ Γ(T, 𝒪_T)` sending a germ to the pullback of a representative.
* `AlgebraicGeometry.Scheme.IdealSheafData.stalkToFormalNeighborhood` — the ring map
  `𝒪_{Y, y} ⟶ A` above.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.stalkToFormalNeighborhood_mem_filtration` — if the
  subscheme cut out by `D` is reduced, the image of `𝔪_y ^ n` lies in the `n`-th step of the
  projection-kernel filtration.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

namespace Scheme.Hom

variable {T Y : Scheme.{u}} (h : T ⟶ Y) (y : Y) (hy : ∀ t : T, h.base t = y)

include hy in
/-- A scheme all of whose points go to `y` lies over every open neighbourhood of `y`. -/
public theorem top_le_preimage_of_forall_base_eq (U : Y.Opens) (hU : y ∈ U) :
    (⊤ : T.Opens) ≤ h ⁻¹ᵁ U := fun t _ ↦ show h.base t ∈ U from (hy t).symm ▸ hU

/-- The pullbacks along `h` of the functions on the open neighbourhoods of `y`, as a cocone on
the diagram computing the stalk `𝒪_{Y, y}`. -/
public def stalkToΓCocone : Cocone ((OpenNhds.inclusion y).op ⋙ Y.presheaf) where
  pt := Γ(T, ⊤)
  ι :=
    { app U := h.appLE U.unop.1 ⊤ (top_le_preimage_of_forall_base_eq h y hy U.unop.1 U.unop.2)
      naturality := fun _ _ _ ↦ (h.map_appLE _ _).trans (Category.comp_id _).symm }

/-- **The pullback of germs at `y` to a scheme lying entirely over `y`**: the germ at `y` of a
function on an open neighbourhood `U` of `y` goes to its pullback along `h`, which is defined on
the whole of `T` because `T` lies over `U`. -/
public def stalkToΓ : Y.presheaf.stalk y ⟶ Γ(T, ⊤) :=
  colimit.desc _ (stalkToΓCocone h y hy)

/-- `AlgebraicGeometry.Scheme.Hom.stalkToΓ` on a germ is the pullback of the function. -/
public theorem germ_stalkToΓ (U : Y.Opens) (hU : y ∈ U) :
    Y.presheaf.germ U y hU ≫ stalkToΓ h y hy =
      h.appLE U ⊤ (top_le_preimage_of_forall_base_eq h y hy U hU) :=
  colimit.ι_desc (stalkToΓCocone h y hy) (op ⟨U, hU⟩)

/-- Elementwise form of `AlgebraicGeometry.Scheme.Hom.germ_stalkToΓ`: the germ of a section `s`
goes to the pullback of `s` along `h`. -/
@[simp]
public theorem stalkToΓ_germ (U : Y.Opens) (hU : y ∈ U) (s : Γ(Y, U)) :
    (stalkToΓ h y hy).hom (Y.presheaf.germ U y hU s) =
      (h.appLE U ⊤ (top_le_preimage_of_forall_base_eq h y hy U hU)).hom s :=
  ConcreteCategory.congr_hom (germ_stalkToΓ h y hy U hU) s

/-- **Naturality of `stalkToΓ` in the source**: precomposing `h` with `φ : T' ⟶ T` composes the
map with the pullback `φ^# : Γ(T, 𝒪_T) ⟶ Γ(T', 𝒪_{T'})`. -/
public theorem stalkToΓ_comp {T' : Scheme.{u}} (φ : T' ⟶ T)
    (hy' : ∀ t : T', (φ ≫ h).base t = y) :
    stalkToΓ (φ ≫ h) y hy' = stalkToΓ h y hy ≫ φ.appTop := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hU ↦ ?_
  have htop : φ.appTop = φ.appLE ⊤ ⊤ (by simp) := φ.appLE_eq_app.symm
  rw [germ_stalkToΓ (φ ≫ h) y hy', ← Category.assoc, germ_stalkToΓ h y hy, htop]
  exact (Scheme.Hom.appLE_comp_appLE φ h U ⊤ ⊤ _ _).symm

end Scheme.Hom

namespace Scheme.IdealSheafData

variable {X Y : Scheme.{u}} (D : X.IdealSheafData) (f : X ⟶ Y) (y : Y)
  (hmaps : ∀ x ∈ (D.support : Set X), f.base x = y)

include hmaps in
/-- Every point of every thickening of `D` goes to `y`. -/
public theorem base_thickening_eq (n : ℕ) (t : thickening D n) :
    ((D ^ (n + 1)).subschemeι ≫ f).base t = y := by
  refine hmaps _ ?_
  have : (D ^ (n + 1)).subschemeι.base t ∈ (D ^ (n + 1)).support :=
    (range_subschemeι (D ^ (n + 1))).le ⟨t, rfl⟩
  rwa [support_pow_succ] at this

/-- The pullback of germs at `y` to the `(n + 1)`-st thickening of `D`. -/
public def stalkToThickening (n : ℕ) : Y.presheaf.stalk y ⟶ Γ(thickening D n, ⊤) :=
  Scheme.Hom.stalkToΓ ((D ^ (n + 1)).subschemeι ≫ f) y (base_thickening_eq D f y hmaps n)

/-- The pullbacks of germs to successive thickenings are compatible with restriction. -/
public theorem thickeningRestriction_stalkToThickening (n : ℕ) (a : Y.presheaf.stalk y) :
    thickeningRestriction D n ((stalkToThickening D f y hmaps (n + 1)).hom a) =
      (stalkToThickening D f y hmaps n).hom a := by
  have hle : D ^ (n + 2) ≤ D ^ (n + 1) :=
    le_def.mpr (fun U ↦ by
      simp only [ideal_pow]
      exact Ideal.pow_le_pow_right (by omega))
  have key : stalkToThickening D f y hmaps n =
      stalkToThickening D f y hmaps (n + 1) ≫ (inclusion hle).appTop := by
    unfold stalkToThickening
    rw [← Scheme.Hom.stalkToΓ_comp _ _ (base_thickening_eq D f y hmaps (n + 1)) (inclusion hle)
      (fun t ↦ by
        rw [← Category.assoc, inclusion_subschemeι]
        exact base_thickening_eq D f y hmaps n t)]
    congr 1
    rw [← Category.assoc, inclusion_subschemeι]
  rw [key]
  rfl

/-- **The ring map `𝒪_{Y, y} ⟶ lim H⁰(Eₙ, 𝒪_{Eₙ})`**: a germ at `y` goes to the compatible family
of its pullbacks to the thickenings of `D`. -/
public def stalkToFormalNeighborhood : Y.presheaf.stalk y →+* formalNeighborhoodRing D where
  toFun a := ⟨fun n ↦ (stalkToThickening D f y hmaps n).hom a,
    fun n ↦ thickeningRestriction_stalkToThickening D f y hmaps n a⟩
  map_one' := Subtype.ext (funext fun _ ↦ map_one _)
  map_mul' a b := Subtype.ext (funext fun _ ↦ map_mul _ a b)
  map_zero' := Subtype.ext (funext fun _ ↦ map_zero _)
  map_add' a b := Subtype.ext (funext fun _ ↦ map_add _ a b)

/-- The `n`-th component of `stalkToFormalNeighborhood D f y hmaps a` is the pullback of the germ
`a` to the `(n + 1)`-st thickening of `D`. -/
@[simp]
public theorem formalNeighborhoodProjection_stalkToFormalNeighborhood (n : ℕ)
    (a : Y.presheaf.stalk y) :
    formalNeighborhoodProjection D n (stalkToFormalNeighborhood D f y hmaps a) =
      (stalkToThickening D f y hmaps n).hom a :=
  rfl

/-- **A germ vanishing at `y` vanishes on the reduced curve.** If the subscheme cut out by `D` is
reduced, the image of the maximal ideal of `𝒪_{Y, y}` lies in the first step of the
projection-kernel filtration: the pullback of such a germ vanishes at every point of the
subscheme, and on a reduced scheme a function vanishing at every point is zero. -/
public theorem stalkToFormalNeighborhood_mem_filtration_one [IsReduced D.subscheme]
    {a : Y.presheaf.stalk y} (ha : a ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) :
    stalkToFormalNeighborhood D f y hmaps a ∈ formalNeighborhoodFiltration D 1 := by
  rw [mem_formalNeighborhoodFiltration_succ_iff]
  obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.germ_exist _ a
  have hyU : y ∉ Y.basicOpen s := by
    rw [Scheme.mem_basicOpen]
    exact ha
  have hsub : D ^ (0 + 1) = D := pow_one D
  show (stalkToThickening D f y hmaps 0).hom (Y.presheaf.germ U y hU s) = 0
  unfold stalkToThickening
  rw [Scheme.Hom.stalkToΓ_germ]
  have : IsReduced (thickening D 0) := by
    show IsReduced (D ^ (0 + 1)).subscheme
    rw [hsub]
    infer_instance
  refine eq_zero_of_basicOpen_eq_bot _ ?_
  rw [Scheme.basicOpen_appLE]
  refine eq_bot_iff.mpr fun t ht ↦ hyU ?_
  have ht' : t ∈ ((D ^ (0 + 1)).subschemeι ≫ f) ⁻¹ᵁ Y.basicOpen s := ht.2
  have := base_thickening_eq D f y hmaps 0 t
  rw [← this]
  exact ht'

/-- **The image of `𝔪_y ^ n` lies in the `n`-th step of the filtration**, for `D` with reduced
subscheme: the first step contains the image of `𝔪_y`, and the filtration is multiplicative. -/
public theorem map_maximalIdeal_pow_le_formalNeighborhoodFiltration [IsReduced D.subscheme]
    (n : ℕ) :
    Ideal.map (stalkToFormalNeighborhood D f y hmaps)
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ n) ≤ formalNeighborhoodFiltration D n := by
  rw [Ideal.map_pow]
  induction n with
  | zero => simp
  | succ m ih =>
    rw [pow_succ]
    refine (Ideal.mul_mono ih ?_).trans (formalNeighborhoodFiltration_mul_le D m 1)
    rw [Ideal.map_le_iff_le_comap]
    exact fun b hb ↦ stalkToFormalNeighborhood_mem_filtration_one D f y hmaps hb

/-- Elementwise form of
`AlgebraicGeometry.Scheme.IdealSheafData.map_maximalIdeal_pow_le_formalNeighborhoodFiltration`. -/
public theorem stalkToFormalNeighborhood_mem_filtration [IsReduced D.subscheme] (n : ℕ)
    {a : Y.presheaf.stalk y}
    (ha : a ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ n) :
    stalkToFormalNeighborhood D f y hmaps a ∈ formalNeighborhoodFiltration D n :=
  map_maximalIdeal_pow_le_formalNeighborhoodFiltration D f y hmaps n (Ideal.mem_map_of_mem _ ha)

end Scheme.IdealSheafData

end AlgebraicGeometry

end
