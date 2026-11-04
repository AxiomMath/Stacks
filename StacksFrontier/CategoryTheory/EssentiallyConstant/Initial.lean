module

public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import StacksFrontier.CategoryTheory.EssentiallyConstant.ProObject

/-! # Essentially constant cofiltered systems and initial functors

Stacks 0A1T (Lemma 4.22.13): if `H : I ⥤ J` is an initial functor between cofiltered
categories, then for every diagram `M : J ⥤ C` the diagram `M` is essentially constant if and
only if `H ⋙ M` is. `IsEssentiallyConstantPro` is the cofiltered notion of Stacks
05PU(2): a cone `(X, α)` on `M`, an index `i₀` and a retraction `r : M.obj i₀ ⟶ X` of `α_{i₀}`,
coherent in the sense that every `M.map v` factors as `M.map u ≫ r ≫ α_j`.

The easy direction, `essentiallyConstant_of_comp_initial`, transports a cone along
`Functor.Initial.extendCone`; the other direction whiskers the cone by `H` and gets its
coherence clause from `coherence_lift_full`, which combines the connectedness of the
costructured-arrow categories `CostructuredArrow H -` with cofilteredness of `I`.
-/

@[expose] public section


open CategoryTheory CategoryTheory.Limits CategoryTheory.EssentiallyConstantPro

-- Background and context.
--
-- Definition 1 (Cofiltered category). A category `I` is cofiltered if it is nonempty and:
--   (1) for every pair of objects `i, i'` there is `k` with morphisms `k → i` and `k → i'`;
--   (2) for every pair of parallel morphisms `a, b : i → i'` there is `c : k → i` with
--       `a ∘ c = b ∘ c`.
-- Equivalently, `I` is cofiltered iff `Iᵒᵖ` is filtered. This is
-- `CategoryTheory.IsCofiltered` in Mathlib, used here as a typeclass.
--
-- Definition 2 (Initial functor). A functor `H : I ⥤ J` is *initial* if for every object
-- `j` of `J` the comma category whose objects are pairs `(i, f)` with `f : H(i) → j`
-- (`CategoryTheory.CostructuredArrow H j`) is connected. This is exactly
-- `CategoryTheory.Functor.Initial`, used here as the typeclass `H.Initial`.
-- (The arrows point `H(i) → j`, the limit/pro-object orientation; this is *not* the
-- dual `Final`/cofinal notion with arrows `j → H(i)`.)
--
-- Definition 3 (Essentially constant cofiltered diagram — Stacks Tag 05PU(2)).
-- Let `M : I ⥤ C` with `I` cofiltered. `M` is *essentially constant with value `X`* if
-- there exist:
--   * an object `X` of `C`,
--   * a cone `(X, {α_i : X → M_i})` for `M` (so `M(φ) ∘ α_i = α_{i'}` for all `φ : i → i'`),
--   * an object `i₀` of `I`, and
--   * a morphism `r : M_{i₀} → X`,
-- such that:
--   (1) (retraction) `r ∘ α_{i₀} = id_X`; and
--   (2) (coherence) for every object `j` there exist `k`, `u : k → i₀`, `v : k → j` with
--       `M(v) = α_j ∘ r ∘ M(u) : M_k → M_j`.
-- `M` is *essentially constant* if there exists such an `X`.
--
-- Below we encode a cone `(X, {α_i})` as a `CategoryTheory.Limits.Cone M`, with
-- `c.pt = X` and `c.π.app i = α_i : X → M_i` (naturality of `c.π` is precisely the cone
-- compatibility `M(φ) ∘ α_i = α_{i'}`). Composition is written in diagrammatic order
-- (`f ≫ g = g ∘ f`), so the retraction `r ∘ α_{i₀} = id_X` becomes `α_{i₀} ≫ r = 𝟙 X`
-- and the coherence `M(v) = α_j ∘ r ∘ M(u)` becomes `M.map v = M.map u ≫ r ≫ c.π.app j`.
-- This is `CategoryTheory.EssentiallyConstantPro.IsEssentiallyConstantPro`.

set_option backward.isDefEq.respectTransparency false in
/-- **Backward direction (←) of Stacks Tag 0A1T.** If `H ⋙ M` is essentially constant then so
is `M`. This is the easy direction: a direct cone transport along the initial functor `H`, with
no extra cofilteredness needed.

Mathematical argument. Let `(c', i₀, r')` witness essential constancy of `H ⋙ M`:
`c' : Cone (H ⋙ M)` with apex `X = c'.pt`, retraction `r' : M(H i₀) → X` with
`c'.π.app i₀ ≫ r' = 𝟙` and the `I`-coherence. We transport `c'` to a cone on `M` by the
canonical extension of cones along an initial functor, `Functor.Initial.extendCone`
(its apex is again `X`, and `extendCone_obj_π_app'` says `(extendCone c').π.app Y = c'.π.app X ≫
M.map f`
for any `f : H X → Y`). Take the new retraction point `j₀ := H i₀` and `r := r'`.
* Retraction: applying `extendCone_obj_π_app'` with the identity `𝟙 (H i₀)` gives
  `(extendCone c').π.app (H i₀) = c'.π.app i₀`, so `(extendCone c').π.app (H i₀) ≫ r' = 𝟙`.
* Coherence: for `j : J`, write `iⱼ := Initial.lift H j` and `hⱼ := Initial.homToLift H j : H iⱼ →
j`;
  then `(extendCone c').π.app j = c'.π.app iⱼ ≫ M.map hⱼ`. Apply the `I`-coherence of `c'` at `iⱼ`
  to get `kᵢ, uᵢ : kᵢ → i₀, vᵢ : kᵢ → iⱼ` with
  `M(H vᵢ) = M(H uᵢ) ≫ r' ≫ c'.π.app iⱼ`. Then `k := H kᵢ`, `u := H uᵢ : H kᵢ → H i₀ = j₀`,
  `v := H vᵢ ≫ hⱼ : H kᵢ → j` work: post-composing the `I`-coherence equation by `M.map hⱼ` gives
  exactly `M v = M u ≫ r ≫ (extendCone c').π.app j`. -/
theorem essentiallyConstant_of_comp_initial
    {C : Type*} [Category C]
    {I J : Type*} [Category I] [Category J]
    [IsCofiltered I] [IsCofiltered J]
    (H : I ⥤ J) [H.Initial] (M : J ⥤ C) :
    IsEssentiallyConstantPro (H ⋙ M) → IsEssentiallyConstantPro M := by
  rintro ⟨c', i₀, r', hretr, hcoh⟩
  refine ⟨Functor.Initial.extendCone.obj c', H.obj i₀, r', ?_, ?_⟩
  · -- retraction
    have hpi : (Functor.Initial.extendCone.obj c').π.app (H.obj i₀) = c'.π.app i₀ := by
      simp
    rw [hpi]; exact hretr
  · -- coherence
    intro j
    set iⱼ := Functor.Initial.lift H j with hiⱼ
    set hⱼ : H.obj iⱼ ⟶ j := Functor.Initial.homToLift H j with hhⱼ
    have hcj : (Functor.Initial.extendCone.obj c').π.app j = c'.π.app iⱼ ≫ M.map hⱼ := by
      simpa using Functor.Initial.extendCone_obj_π_app' (F := H) (G := M) c' (X := iⱼ) hⱼ
    obtain ⟨kI, uI, vI, hkuv⟩ := hcoh iⱼ
    refine ⟨H.obj kI, H.map uI, H.map vI ≫ hⱼ, ?_⟩
    rw [hcj]
    simp only [Functor.comp_map] at hkuv
    rw [M.map_comp, hkuv]
    simp

/-- Propagating a coherence-lift witness along the connected category `CostructuredArrow H T`
from a base arrow `Y₀` to any `Y`, using cofilteredness of `I`. -/
private theorem exists_lift_of_base
    {I J : Type*} [Category I] [Category J] [IsCofiltered I]
    (H : I ⥤ J) [H.Initial] {j₀ : J} (i₁ : I) (f₁ : H.obj i₁ ⟶ j₀) {T m : J}
    (a : m ⟶ j₀) (b : m ⟶ T) (Y₀ Y : CostructuredArrow H T)
    (base : ∃ (k : I) (u : k ⟶ i₁) (v : k ⟶ Y₀.left) (w : H.obj k ⟶ m),
      H.map u ≫ f₁ = w ≫ a ∧ H.map v ≫ Y₀.hom = w ≫ b) :
    ∃ (k : I) (u : k ⟶ i₁) (v : k ⟶ Y.left) (w : H.obj k ⟶ m),
      H.map u ≫ f₁ = w ≫ a ∧ H.map v ≫ Y.hom = w ≫ b := by
  refine (isPreconnected_induction
      (fun Y => ∃ (k : I) (u : k ⟶ i₁) (v : k ⟶ Y.left) (w : H.obj k ⟶ m),
        H.map u ≫ f₁ = w ≫ a ∧ H.map v ≫ Y.hom = w ≫ b)
      ?_ ?_ base Y).some
  · rintro Y₁ Y₂ φ ⟨k, u, v, w, ha, hbb⟩
    refine ⟨k, u, v ≫ φ.left, w, ha, ?_⟩
    rw [H.map_comp, Category.assoc, CostructuredArrow.w φ, hbb]
  · rintro Y₁ Y₂ φ ⟨k, u, v, w, ha, hbb⟩
    obtain ⟨s, α, β, hαβ⟩ := IsCofiltered.cospan v φ.left
    refine ⟨s, α ≫ u, β, H.map α ≫ w, ?_, ?_⟩
    · rw [H.map_comp, Category.assoc, ha, ← Category.assoc]
    · rw [Category.assoc, ← hbb, ← Category.assoc, ← H.map_comp, hαβ, H.map_comp,
        Category.assoc, CostructuredArrow.w φ]

/-- Auxiliary "coherence lift" for arrows into `j₀`. Given the chosen base costructured arrow
`(i₁, f₁) : CostructuredArrow H j₀` and any other costructured arrow `Y = (Y.left, Y.hom)` into
`j₀`, the connectedness of `CostructuredArrow H j₀` (since `H` is initial) together with
cofilteredness of `I` produces a common lower bound `k` mapping to `i₁` and to `Y.left` whose
`H`-images agree after post-composition: `H u ≫ f₁ = H v ≫ Y.hom`. Proved by
`isPreconnected_induction` on `CostructuredArrow H j₀`. -/
theorem coherence_lift_aux
    {I J : Type*} [Category I] [Category J] [IsCofiltered I]
    (H : I ⥤ J) [H.Initial] (j₀ : J) (i₁ : I) (f₁ : H.obj i₁ ⟶ j₀)
    (Y : CostructuredArrow H j₀) :
    ∃ (k : I) (u : k ⟶ i₁) (v : k ⟶ Y.left), H.map u ≫ f₁ = H.map v ≫ Y.hom := by
  obtain ⟨k, u, v, w, h1, h2⟩ := exists_lift_of_base H i₁ f₁ (𝟙 j₀) (𝟙 j₀)
    (CostructuredArrow.mk f₁) Y ⟨i₁, 𝟙 i₁, 𝟙 i₁, f₁, by simp⟩
  exact ⟨k, u, v, by simpa [h2] using h1⟩

/-- Full "coherence lift". Given the `J`-coherence data `(kⱼ, uⱼ, vⱼ)` for the object `H i`
(so `vⱼ : kⱼ ⟶ H i`, `uⱼ : kⱼ ⟶ j₀`) and any costructured arrow `Y` into `H i`, produce a
common `k : I` with `u : k ⟶ i₁`, `v : k ⟶ Y.left` and a connecting `w : H k ⟶ kⱼ` satisfying
the two compatibility equations `H u ≫ f₁ = w ≫ uⱼ` and `H v ≫ Y.hom = w ≫ vⱼ`. Proved by
`isPreconnected_induction` on `CostructuredArrow H (H.obj i)`, with the base case fed by
`coherence_lift_aux` applied to `(b, g ≫ uⱼ)` for a witness `(b, g)` of
`CostructuredArrow H kⱼ`. -/
theorem coherence_lift_full
    {I J : Type*} [Category I] [Category J] [IsCofiltered I]
    (H : I ⥤ J) [H.Initial] (j₀ : J) (i₁ : I) (f₁ : H.obj i₁ ⟶ j₀)
    (i : I) (kⱼ : J) (uⱼ : kⱼ ⟶ j₀) (vⱼ : kⱼ ⟶ H.obj i)
    (Y : CostructuredArrow H (H.obj i)) :
    ∃ (k : I) (u : k ⟶ i₁) (v : k ⟶ Y.left) (w : H.obj k ⟶ kⱼ),
      H.map u ≫ f₁ = w ≫ uⱼ ∧ H.map v ≫ Y.hom = w ≫ vⱼ := by
  obtain ⟨B⟩ := (inferInstance : Nonempty (CostructuredArrow H kⱼ))
  obtain ⟨k₀, u₀, v₀, heq₀⟩ :=
    coherence_lift_aux H j₀ i₁ f₁ (CostructuredArrow.mk (B.hom ≫ uⱼ) (S := H))
  refine exists_lift_of_base H i₁ f₁ uⱼ vⱼ (CostructuredArrow.mk (B.hom ≫ vⱼ)) Y
    ⟨k₀, u₀, v₀, H.map v₀ ≫ B.hom, ?_, by simp⟩
  simpa [Category.assoc] using heq₀

/-- **Forward direction (→) of Stacks Tag 0A1T.** If `M` is essentially constant then so is
`H ⋙ M`. This is the harder direction: the retraction clause is immediate from cone
compatibility, while the coherence clause needs the coherence lift `coherence_lift_full`.

Mathematical argument. Let `(c, j₀, r)` witness essential constancy of `M`: `c : Cone M`,
`r : M(j₀) → X` (`X = c.pt`) with `c.π.app j₀ ≫ r = 𝟙` and the `J`-coherence. Whisker `c` along
`H` to get `c.whisker H : Cone (H ⋙ M)` (apex `X`, `(c.whisker H).π.app i = c.π.app (H i)`).
Since `H` is initial, `CostructuredArrow H j₀` is connected, hence nonempty: pick
`i₁ : I` and `f₁ : H i₁ → j₀`. Take retraction point `i₁` and retraction `r₁ := M f₁ ≫ r`.
* Retraction: `(c.whisker H).π.app i₁ ≫ r₁ = c.π.app (H i₁) ≫ M f₁ ≫ r`; by cone
  compatibility `c.w f₁` this equals `c.π.app j₀ ≫ r = 𝟙`.
* Coherence: fix `i : I`. We must produce `k : I`, `u : k → i₁`, `v : k → i`
  with `M(H v) = M(H u) ≫ M f₁ ≫ r ≫ c.π.app (H i)`, i.e. `M(H v) = M(H u ≫ f₁) ≫ R`, where
  `R := r ≫ c.π.app (H i) : M j₀ → M (H i)`.
  Apply the `J`-coherence of `c` at the object `H i ∈ J`: obtain `kⱼ : J`, `uⱼ : kⱼ → j₀`,
  `vⱼ : kⱼ → H i` with `M vⱼ = M uⱼ ≫ R`. It therefore suffices to find `k : I`, `u : k → i₁`,
  `v : k → i`, and a *connecting* arrow `w : H k → kⱼ` such that, **as morphisms of `J`**,
    (a) `H u ≫ f₁ = w ≫ uⱼ`   (both `H k → j₀`)   and   (b) `H v = w ≫ vⱼ`   (both `H k → H i`),
  because then `M(H v) = M w ≫ M vⱼ = M w ≫ M uⱼ ≫ R = M(H u ≫ f₁) ≫ R`, as required.
  The data `(k, u, v, w)` is obtained from the *connectedness* of the costructured-arrow
  categories `CostructuredArrow H j₀` and `CostructuredArrow H (H i)` together with the
  cofilteredness of `I`: starting from a nonempty witness `b : I`, `g : H b → kⱼ` of
  `CostructuredArrow H kⱼ`, the two objects `⟨b, g ≫ vⱼ⟩` and the canonical `⟨i, 𝟙 (H i)⟩`
  of `CostructuredArrow H (H i)` lie in one connected component; following the zigzag and
  taking a cofiltered lower bound in `I` (using `IsCofiltered.min`/`cospan`/`cone_maps`)
  yields a single `k : I` mapping compatibly to `b` and to `i`, producing `v : k → i` and
  `w : H k → kⱼ` with (b); the same lower-bounding applied to `g ≫ uⱼ : H b → j₀` and `f₁`
  produces `u : k → i₁` with (a). (Equivalently, this is the `Hom(-, X)`/limit characterization
  of essential constancy, Stacks 05PZ: `H` initial gives `Hᵒᵖ` final via
  `Functor.final_op_of_initial`, so
`Functor.Final.colimitIso`/`Functor.Initial.isLimitWhiskerEquiv`
  identify the relevant colimit/limit comparisons; either route also works.) -/
theorem essentiallyConstant_comp_initial_of
    {C : Type*} [Category C]
    {I J : Type*} [Category I] [Category J]
    [IsCofiltered I] [IsCofiltered J]
    (H : I ⥤ J) [H.Initial] (M : J ⥤ C) :
    IsEssentiallyConstantPro M → IsEssentiallyConstantPro (H ⋙ M) := by
  rintro ⟨c, j₀, r, hretr, hcoh⟩
  obtain ⟨A⟩ := (inferInstance : Nonempty (CostructuredArrow H j₀))
  set i₁ : I := A.left with hi₁
  set f₁ : H.obj i₁ ⟶ j₀ := A.hom with hf₁
  refine ⟨Cone.whisker H c, i₁, M.map f₁ ≫ r, ?_, ?_⟩
  · -- retraction
    have hw : c.π.app (H.obj i₁) ≫ M.map f₁ = c.π.app j₀ := c.w f₁
    dsimp only [Cone.whisker_pt, Cone.whisker_π, Functor.whiskerLeft_app]
    rw [← Category.assoc, hw, hretr]
  · -- coherence
    intro i
    -- Apply the `J`-coherence of `c` at the object `H i`.
    obtain ⟨kⱼ, uⱼ, vⱼ, hkuv⟩ := hcoh (H.obj i)
    -- Coherence-lift via connectedness of `CostructuredArrow H -` + cofilteredness of `I`,
    -- applied to the canonical costructured arrow `(i, 𝟙 (H i))`.
    obtain ⟨k, u, v, w, ha, hbb⟩ :=
      coherence_lift_full H j₀ i₁ f₁ i kⱼ uⱼ vⱼ (CostructuredArrow.mk (𝟙 (H.obj i)) (S := H))
    refine ⟨k, u, v, ?_⟩
    dsimp only [Functor.comp_map, Cone.whisker_π, Functor.whiskerLeft_app]
    have hbb' : H.map v = w ≫ vⱼ := by simpa using hbb
    have hcalc : M.map (H.map v) = M.map w ≫ M.map vⱼ := by rw [hbb', M.map_comp]
    rw [hcalc, hkuv, ← Category.assoc, ← M.map_comp, ← ha, M.map_comp]
    simp

/-- Stacks Tag 0A1T (Lemma 4.22.13). For cofiltered `I`, `J`, an initial functor
`H : I ⥤ J`, and any diagram `M : J ⥤ C`, the diagram `M` is essentially constant iff its
restriction `H ⋙ M` along `H` is essentially constant.

Proved by combining the two directions: `essentiallyConstant_comp_initial_of` (→) and
`essentiallyConstant_of_comp_initial` (←). -/
@[stacks 0A1T]
theorem essentiallyConstant_iff_comp_initial
    {C : Type*} [Category C]
    {I J : Type*} [Category I] [Category J]
    [IsCofiltered I] [IsCofiltered J]
    (H : I ⥤ J) [H.Initial] (M : J ⥤ C) :
    IsEssentiallyConstantPro M ↔ IsEssentiallyConstantPro (H ⋙ M) :=
  ⟨essentiallyConstant_comp_initial_of H M, essentiallyConstant_of_comp_initial H M⟩
