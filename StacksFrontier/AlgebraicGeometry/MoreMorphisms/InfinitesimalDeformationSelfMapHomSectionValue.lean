module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FirstOrderThickeningConormalSelfMap
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalDeformationSheafHomAction

/-!
# The perturbation of a lift under a self-map of the thickening

Let `i : X ⟶ X'` be a first-order thickening, `j : Y ⟶ Y'` an immersion, `a : X ⟶ Y`, and let
`b : V ⟶ Y'` be a lift of `a` over an open `V` of `X'`. A section `θ` of
`SheafHom_{𝒪_X}(a^*Ω_{Y/S}, 𝒞_{X/X'})` perturbs `b` by the derivation
`Stacks.Thickenings.homSectionValue`, which is the composite

`Γ(Y', W) --j^♯--> Γ(Y, j⁻¹W) --d--> Γ(a^*Ω_{Y/S}, ·) --θ--> Γ(𝒞_{X/X'}, ·) ⟶ Γ(X', ·)`.

This file computes what a **self-map** of the two thickenings does to that perturbation. Let
`σ : X' ⟶ X'` fix the closed subscheme (`i ≫ σ = i`), let `w` be a self-map of `V` lying over
it (`w ≫ V.ι = V.ι ≫ σ`), and let `v : Y' ⟶ Y'` fix `Y` (`j ≫ v = j`). Suppose `σ` acts on the
conormal sections as multiplication by a section `r` of `𝒪_X` over `i⁻¹V`, and the second acting
section `θ₂` is `r` times the first. Then

`w^♯ (θ₁ ⬝ d) = θ₂ ⬝ d`

in the precise sense of `Stacks.Thickenings.homSectionValue_comm_of_conormalSelfMap_eq_smul`,
which is the hypothesis `hθ` of `Stacks.Thickenings.homSectionAct_comp_of_homSectionValue_comm`
and of `Stacks.Thickenings.liftsOverBaseVAddOfBase_comp_of_homSectionValue_comm` at a self-map of
one situation. That is the step which turns a computation of the self-map on the conormal sheaf
— for the scaling `ε ↦ cε` of a first-order deformation,
`Deformation.Examples.conormalSelfMap_eq_smul` — into naturality of the action of [Stacks
Project, Tag 0CK2], and so into the `k`-homogeneity half of the `k`-linearity asserted in [Stacks
Project, Tag 0E3V].

## Main results

* `Stacks.Thickenings.image_preimage_le_preimage_of_comp_ι`: the image of a `w`-preimage lies in
  the `σ`-preimage of the image, for `w` lying over `σ` along the inclusion of `V`.
* `Stacks.Thickenings.app_eq_app_comp_map`: **the comorphism of `w` is the comorphism of `σ`**,
  read over the image open and followed by a restriction of sections. This is the only place the
  passage between an open subscheme and its ambient scheme happens.
* `Stacks.Thickenings.app_conormalSection_of_comp_ι`: `w^♯` carries a conormal section to the
  conormal section of `Stacks.Thickenings.conormalSelfMap` of it.
* `Stacks.Thickenings.homSectionValue_comm_of_conormalSelfMap_eq_smul`: **the perturbation
  commutes with the self-maps**, when the self-map scales the conormal sections by `r` and the
  second acting section is `r` times the first.

## Implementation notes

The scalar is carried as a section `r` of `𝒪_X` over `i⁻¹V` together with two hypotheses saying
how it acts — on the conormal sections through
`Stacks.Thickenings.conormalSelfMap`, and on the values of the acting sections — rather than as
an element of a ring acting on `Stacks.Thickenings.moduleHomSections`. That is deliberate: the
hom-sections of a sheaf of homomorphisms carry no scalar action over any open in the library
(only the transported `k`-structure at `⊤` of
`Deformation.Examples.deformationHomSectionsTopModule`), so a statement about `c • θ` would have
to name a module structure that does not exist at a general `V`. Both hypotheses are restriction
statements about one section, which is exactly what a consumer can supply: for a self-arrow of a
first-order deformation, `Deformation.Examples.conormalSelfMap_eq_smul` gives the first with
`r` the function `Deformation.Examples.baseSection` attaches to the residue of the scalar.

## References

* [Stacks Project, Tag 04BZ](https://stacks.math.columbia.edu/tag/04BZ)
* [Stacks Project, Tag 0CK1](https://stacks.math.columbia.edu/tag/0CK1)
* [Stacks Project, Tag 0CK2](https://stacks.math.columbia.edu/tag/0CK2)
* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Thickenings

/-! ### A self-map of an open subscheme lying over a self-map of the ambient scheme -/

section SelfMap

variable {X' : Scheme.{u}} {V : X'.Opens} {σ : X' ⟶ X'} {w : V.toScheme ⟶ V.toScheme}

/-- **The image of a `w`-preimage lies in the `σ`-preimage of the image.** For a self-map `w` of
an open `V` of `X'` lying over a self-map `σ` of `X'`, a point of `V` carried into `U` by `w` is
carried into the image of `U` by `σ`. -/
theorem image_preimage_le_preimage_of_comp_ι (hw : w ≫ V.ι = V.ι ≫ σ) (U : V.toScheme.Opens) :
    V.ι ''ᵁ (w ⁻¹ᵁ U) ≤ σ ⁻¹ᵁ (V.ι ''ᵁ U) := by
  rintro x ⟨y, hy, rfl⟩
  show σ.base (V.ι.base y) ∈ V.ι ''ᵁ U
  have hy' : (w ≫ V.ι).base y ∈ V.ι ''ᵁ U := (Scheme.Opens.mem_ι_image_iff V).2 hy
  rw [hw] at hy'
  exact hy'

/-- **The comorphism of `w` is the comorphism of `σ` over the image open.** The sections of
`𝒪_V` over `U` are the sections of `𝒪_{X'}` over `V.ι ''ᵁ U`, and under that identification the
component of `w^♯` over `U` is the component of `σ^♯` over `V.ι ''ᵁ U` followed by restriction
along `Stacks.Thickenings.image_preimage_le_preimage_of_comp_ι`.

Both sides are read as a composite of `AlgebraicGeometry.Scheme.Hom.appLE`s of the two equal
morphisms `w ≫ V.ι` and `V.ι ≫ σ`; the two components of `V.ι` that appear are restrictions of
sections of `𝒪_{X'}`, by `AlgebraicGeometry.Scheme.Opens.ι_appLE`, and the one on the left is
the identity. -/
theorem app_eq_app_comp_map (hw : w ≫ V.ι = V.ι ≫ σ) (U : V.toScheme.Opens) :
    w.app U = σ.app (V.ι ''ᵁ U) ≫
      X'.presheaf.map (homOfLE (image_preimage_le_preimage_of_comp_ι hw U)).op := by
  have e₁ : U ≤ V.ι ⁻¹ᵁ (V.ι ''ᵁ U) := (V.ι.preimage_image_eq U).ge
  have e₂ : w ⁻¹ᵁ U ≤ V.ι ⁻¹ᵁ (σ ⁻¹ᵁ (V.ι ''ᵁ U)) :=
    (V.ι.preimage_image_eq (w ⁻¹ᵁ U)).ge.trans
      (Scheme.Hom.preimage_mono _ (image_preimage_le_preimage_of_comp_ι hw U))
  have h1 := Scheme.Hom.appLE_comp_appLE w V.ι (V.ι ''ᵁ U) U (w ⁻¹ᵁ U) e₁ le_rfl
  have h2 := Scheme.Hom.appLE_comp_appLE V.ι σ (V.ι ''ᵁ U) (σ ⁻¹ᵁ (V.ι ''ᵁ U)) (w ⁻¹ᵁ U)
    le_rfl e₂
  have hM := appLE_congr_hom hw (V.ι ''ᵁ U) (w ⁻¹ᵁ U) (w.preimage_mono e₁) e₂
  have hid : X'.presheaf.map (homOfLE (le_refl (V.ι ''ᵁ U))).op = 𝟙 Γ(V.toScheme, U) := by
    rw [Subsingleton.elim (homOfLE (le_refl (V.ι ''ᵁ U))) (𝟙 _)]
    exact CategoryTheory.Functor.map_id _ _
  rw [Scheme.Opens.ι_appLE] at h1 h2
  rw [hid] at h1
  have h1' : w.appLE U (w ⁻¹ᵁ U) le_rfl
      = (w ≫ V.ι).appLE (V.ι ''ᵁ U) (w ⁻¹ᵁ U) (w.preimage_mono e₁) := by
    rw [← h1]
    exact (Category.id_comp _).symm
  rw [Scheme.Hom.app_eq_appLE (f := w), h1', hM, ← h2, Scheme.Hom.appLE_eq_app]
  rfl

end SelfMap

/-! ### The self-map on the conormal sections -/

section Conormal

variable {X X' : Scheme.{u}} {i : X ⟶ X'} [IsClosedImmersion i] {V : X'.Opens}
  {σ : X' ⟶ X'} {w : V.toScheme ⟶ V.toScheme}

/-- **`w^♯` of a conormal section is the conormal section of
`Stacks.Thickenings.conormalSelfMap` of it.** This is
`Stacks.Thickenings.conormalSection_conormalSelfMap` — the characterising property of the induced
endomorphism — read through `Stacks.Thickenings.app_eq_app_comp_map` and restricted from the
`σ`-preimage of the image open to the image of the `w`-preimage. -/
theorem app_conormalSection_of_comp_ι (hsq : i.ker ^ 2 = ⊥) (hσ : i ≫ σ = i)
    (hw : w ≫ V.ι = V.ι ≫ σ) (U : V.toScheme.Opens)
    (x : Γ(conormalModules i, i ⁻¹ᵁ (V.ι ''ᵁ U))) :
    (w.app U).hom (conormalSection hsq (V.ι ''ᵁ U) x)
      = conormalSection hsq (V.ι ''ᵁ (w ⁻¹ᵁ U))
          ((conormalModules i).presheaf.map
            (homOfLE ((i.preimage_mono (image_preimage_le_preimage_of_comp_ι hw U)).trans
              (preimage_preimage_of_comp_eq_self hσ (V.ι ''ᵁ U)).le)).op
            (conormalSelfMap hsq hσ (V.ι ''ᵁ U) x)) := by
  have hsplit : (w.app U).hom (conormalSection hsq (V.ι ''ᵁ U) x)
      = (X'.presheaf.map (homOfLE (image_preimage_le_preimage_of_comp_ι hw U)).op).hom
          ((σ.app (V.ι ''ᵁ U)).hom (conormalSection hsq (V.ι ''ᵁ U) x)) := by
    rw [app_eq_app_comp_map hw U]
    rfl
  rw [hsplit, ← conormalSection_conormalSelfMap hsq hσ (V.ι ''ᵁ U) x,
    conormalSection_map hsq (image_preimage_le_preimage_of_comp_ι hw U),
    ← Functor.map_comp_apply]
  rfl

end Conormal

/-! ### The perturbation commutes with the self-maps -/

section Value

variable {S X X' Y Y' : Scheme.{u}} {i : X ⟶ X'} {j : Y ⟶ Y'} {a : X ⟶ Y}
  [IsClosedImmersion i] [IsImmersion j]
  {V : X'.Opens} {b : V.toScheme ⟶ Y'} {σ : X' ⟶ X'} {w : V.toScheme ⟶ V.toScheme}
  {v : Y' ⟶ Y'}

/-- **The perturbation of a lift commutes with a self-map of the thickening that scales the
conormal sections.** Let `i : X ⟶ X'` be a first-order thickening, `b : V ⟶ Y'` a lift of
`a : X ⟶ Y` along `j` over an open `V` of `X'`, and let

* `σ : X' ⟶ X'` fix the closed subscheme, `i ≫ σ = i`;
* `w : V ⟶ V` lie over `σ`, `w ≫ V.ι = V.ι ≫ σ`;
* `v : Y' ⟶ Y'` fix `Y`, `j ≫ v = j`;
* the lift be compatible, `b ≫ v = w ≫ b`.

Suppose `σ` induces multiplication by a section `r` of `𝒪_X` over `i⁻¹V` on the conormal
sections (`hc`), and the acting section `θ₂` is `r` times `θ₁` on sections (`hθ`). Then the two
perturbations `Stacks.Thickenings.homSectionValue` correspond under `w^♯` and `v^♯`.

This is exactly the hypothesis `hθ` of
`Stacks.Thickenings.homSectionAct_comp_of_homSectionValue_comm` and of
`Stacks.Thickenings.liftsOverBaseVAddOfBase_comp_of_homSectionValue_comm`, at one situation with
vertical maps given by the self-maps; so it is what turns a computation of the self-map on the
conormal sheaf into naturality of the action of [Stacks Project, Tag 0CK2].

Nothing is assumed affine, nothing étale, and no scalar action on the acting sheaf is named: see
the implementation notes of this file. -/
theorem homSectionValue_comm_of_conormalSelfMap_eq_smul
    (hsq : i.ker ^ 2 = ⊥) (pY' : Y' ⟶ S) (hσ : i ≫ σ = i)
    (cb : i ∣_ V ≫ b = ((i ⁻¹ᵁ V).ι ≫ a) ≫ j)
    (hw : w ≫ V.ι = V.ι ≫ σ) (hv : j ≫ v = j) (cA : b ≫ v = w ≫ b)
    {θ₁ θ₂ : deformationHomSections i a (j ≫ pY') V} {r : Γ(X, i ⁻¹ᵁ V)}
    (hc : ∀ (A : X'.Opens) (hA : A ≤ V) (x : Γ(conormalModules i, i ⁻¹ᵁ A)),
      conormalSelfMap hsq hσ A x
        = (X.presheaf.map (homOfLE (i.preimage_mono hA)).op).hom r • x)
    (hθ : ∀ (U : X.Opens) (hU : U ≤ i ⁻¹ᵁ V)
        (y : Γ(Smooth.pullbackCotangentSheaf (j ≫ pY') a, U)),
      θ₂.app hU y = (X.presheaf.map (homOfLE hU).op).hom r • θ₁.app hU y)
    (W : Y'.Opens) (s : Γ(Y', W)) :
    (V.toScheme.presheaf.map (eqToHom (preimage_comp_eq cA W)).op).hom
        ((w.app (b ⁻¹ᵁ W)).hom (homSectionValue hsq pY' cb θ₁ W s))
      = homSectionValue hsq pY' cb θ₂ (v ⁻¹ᵁ W) ((v.app W).hom s) := by
  have hjj : j ⁻¹ᵁ (v ⁻¹ᵁ W) = j ⁻¹ᵁ W := congrArg (fun p : Y ⟶ Y' => p ⁻¹ᵁ W) hv
  have hjv : (j.app (v ⁻¹ᵁ W)).hom ((v.app W).hom s)
      = (Y.presheaf.map (homOfLE hjj.le).op).hom ((j.app W).hom s) := by
    have h := appLE_congr_hom hv W (j ⁻¹ᵁ (v ⁻¹ᵁ W)) le_rfl hjj.le
    have h2 := congrArg (fun z : Γ(Y', W) ⟶ Γ(Y, j ⁻¹ᵁ (v ⁻¹ᵁ W)) => z.hom s) h
    simpa [Scheme.Hom.appLE] using h2
  have key1 := app_conormalSection_of_comp_ι hsq hσ hw (b ⁻¹ᵁ W)
      (θ₁.app (preimage_liftOpen_le i V b W)
        (Smooth.pullbackD (j ≫ pY') a (j ⁻¹ᵁ W)
          (preimage_liftOpen_le_preimage cb W) ((j.app W).hom s)))
  rw [hc (liftOpen V b W) (liftOpen_le V b W) _, Scheme.Modules.map_smul] at key1
  have hmap : (V.toScheme.presheaf.map (eqToHom (preimage_comp_eq cA W)).op)
      = X'.presheaf.map (homOfLE (V.ι.image_mono (preimage_comp_eq cA W).le)).op := by
    rw [Scheme.Opens.toScheme_presheaf_map]
    congr 1
  unfold homSectionValue
  rw [key1, hmap]
  refine (conormalSection_map hsq (V.ι.image_mono (preimage_comp_eq cA W).le) _).trans ?_
  rw [Scheme.Modules.map_smul]
  refine congrArg (conormalSection hsq (liftOpen V b (v ⁻¹ᵁ W))) ?_
  have hUA : i ⁻¹ᵁ (liftOpen V b (v ⁻¹ᵁ W)) ≤ a ⁻¹ᵁ (j ⁻¹ᵁ W) :=
    (preimage_liftOpen_le_preimage cb (v ⁻¹ᵁ W)).trans (a.preimage_mono hjj.le)
  rw [hθ (i ⁻¹ᵁ (liftOpen V b (v ⁻¹ᵁ W))) (preimage_liftOpen_le i V b (v ⁻¹ᵁ W)) _, hjv,
    pullbackD_shrink' (j ≫ pY') a hjj.le hUA
      (preimage_liftOpen_le_preimage cb (v ⁻¹ᵁ W)) ((j.app W).hom s)]
  have h₀ : i ⁻¹ᵁ (liftOpen V b W) ≤ a ⁻¹ᵁ (j ⁻¹ᵁ W) := preimage_liftOpen_le_preimage cb W
  have hA'le : i ⁻¹ᵁ (V.ι ''ᵁ (w ⁻¹ᵁ (b ⁻¹ᵁ W))) ≤ i ⁻¹ᵁ (liftOpen V b W) :=
    (i.preimage_mono (image_preimage_le_preimage_of_comp_ι hw (b ⁻¹ᵁ W))).trans
      (preimage_preimage_of_comp_eq_self hσ (liftOpen V b W)).le
  have h₂₁ : i ⁻¹ᵁ (liftOpen V b (v ⁻¹ᵁ W)) ≤ i ⁻¹ᵁ (V.ι ''ᵁ (w ⁻¹ᵁ (b ⁻¹ᵁ W))) :=
    i.preimage_mono (V.ι.image_mono (preimage_comp_eq cA W).le)
  congr 1
  · exact presheaf_map_map_map _ _ _ _ r
  · rw [← moduleHomSections.map_app, ← moduleHomSections.map_app,
      Smooth.map_pullbackD (j ≫ pY') a (j ⁻¹ᵁ W) h₀ (hA'le.trans h₀) hA'le,
      Smooth.map_pullbackD (j ≫ pY') a (j ⁻¹ᵁ W) (hA'le.trans h₀) hUA h₂₁]

end Value

end Stacks.Thickenings

end
