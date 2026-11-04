module

public import StacksFrontier.RingTheory.MilnorPatching.DerivedPatching
public import StacksFrontier.RingTheory.Dualizing.MapDerivedCategoryJunction

/-!
# The glueing map of the proof of Stacks Tag 0DL7

Let `M ∈ D(𝒪_Y)`, `K' ∈ D(𝒪_{X'})` and `α : Lf^* M ⟶ Li^* K'` for a pushout square of algebraic
spaces `Y' = Y ⨿_X X'` with maps `j : Y ⟶ Y'`, `f' : X' ⟶ Y'`, `f : X ⟶ Y`, `i : X ⟶ X'`. The
proof of Stacks Tag 0DL7 takes for `M'` the fibre of the map
`Rj_* M ⊕ Rf'_* K' ⟶ Rj_* Rf_* Li^* K'` whose first component is `Rj_*` of the map
`β : M ⟶ Rf_* Li^* K'` adjoint to `α`, and whose second component is `Rf'_*` of the unit
`K' ⟶ Ri_* Li^* K'` read through `Rf'_* Ri_* = Rj_* Rf_*`. This file defines that map for any two
adjunctions `Lf ⊣ Rf`, `Li ⊣ Ri` and any identification `c : Rf ⋙ Rj ≅ Ri ⋙ Rf'`, and identifies
it, for a fibre product of rings `B' = B ×_A A'` and derived restriction of scalars, with the
second map of the patched short exact sequence `0 → L → E ⊕ P → P ⊗_{A'} A → 0`.

## Main definitions

* `MilnorPatching.glueingMap`: the map `Rj M ⊞ Rf' K' ⟶ Rj (Rf (Li K'))`, with components
  `Rj (adjF.homEquiv α)` and `-(Rf' (adjI.unit K') ≫ c⁻¹)`.
* `MilnorPatching.derivedRestrictCompIso`: the canonical identification of derived restriction
  of scalars along `B' → B → A` with derived restriction along `B' → A' → A`.
* `MilnorPatching.complexDerivedExtensionIso`: the isomorphism `E ⊗ᴸ_B A ≅ P ⊗ᴸ_{A'} A`
  represented by an isomorphism of complexes `φ : E ⊗_B A ≅ P ⊗_{A'} A`.
* `MilnorPatching.glueingSourceIso`, `MilnorPatching.glueingTargetIso`: the identifications of the
  source and target of the glueing map with `E ⊕ P` and `P ⊗_{A'} A`, read in `D(B')`.

## Main results

* `MilnorPatching.biprod_map_comp_glueingMap`: the glueing map is natural in `(M, K', α)`.
* `MilnorPatching.glueingMap_comp_leftAdjointUniq`: changing the two adjunctions (with the same
  right adjoints) changes the glueing map by the induced isomorphism on its target and changes
  `α` accordingly.
* `MilnorPatching.glueingMap_comp_ofNatIsoRight`: replacing the right adjoints by isomorphic
  functors, compatibly with `c`, conjugates the glueing map by the given isomorphisms.
* `MilnorPatching.glueingMap_comp_glueingTargetIso`: **for derived restriction of scalars along
  the maps of a fibre product of rings and the derived change-of-rings adjunctions, the glueing
  map of `(E, P, φ)` is the map `(e, p) ↦ φ (1 ⊗ e) - 1 ⊗ p` of the patched short exact
  sequence.**
* `MilnorPatching.exists_iso_patchedComplex_of_distinguished_glueingMap`: hence the fibre of the
  glueing map is the patched complex `L`, compatibly with the maps to `E ⊕ P`.

## Implementation notes

Derived categories are arbitrary `HasDerivedCategory` instances, derived extension of scalars is
any total left derived functor of degreewise extension of scalars, and its adjunction with derived
restriction of scalars is
`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction` (Stacks Tag 0GMT). The
identification of the two composites of derived restriction of scalars is built from
`Dualizing.mapDerivedCategoryCompNatIso`, whose components at localized complexes are the
degreewise identifications.

The general part of the file is stated for arbitrary adjunctions because that is the form in
which the space-level proof meets it: the comparison of `Lf^*` and `Rf_*` on affine algebraic
spaces with derived extension and restriction of scalars (Stacks Tags 08GH, 08DW, 0DJK) is an
isomorphism of functors, not of adjunctions.

## References

* [Stacks Project, Tag 0DL7](https://stacks.math.columbia.edu/tag/0DL7)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ModuleGlueing

universe w₁ w₂ w₃ w₄ u

namespace MilnorPatching

section Generic

variable {𝒟 𝒟₁ 𝒟₂ 𝒟₀ : Type*} [Category* 𝒟] [Category* 𝒟₁] [Category* 𝒟₂] [Category* 𝒟₀]
  [Preadditive 𝒟] [HasBinaryBiproducts 𝒟]
  {Rj : 𝒟₁ ⥤ 𝒟} {Rf' : 𝒟₂ ⥤ 𝒟} {Lf : 𝒟₁ ⥤ 𝒟₀} {Rf : 𝒟₀ ⥤ 𝒟₁} {Li : 𝒟₂ ⥤ 𝒟₀}
  {Ri : 𝒟₀ ⥤ 𝒟₂}

/-- **The glueing map of the proof of Stacks 0DL7.** For adjunctions `Lf ⊣ Rf` and `Li ⊣ Ri`, an
identification `c : Rf ⋙ Rj ≅ Ri ⋙ Rf'` and `α : Lf M ⟶ Li K'`, the map
`Rj M ⊞ Rf' K' ⟶ Rj (Rf (Li K'))` whose first component is `Rj` of the map `M ⟶ Rf (Li K')`
adjoint to `α`, and whose second component is minus `Rf'` of the unit `K' ⟶ Ri (Li K')` followed
by `c⁻¹`. -/
def glueingMap (adjF : Lf ⊣ Rf) (adjI : Li ⊣ Ri) (c : Rf ⋙ Rj ≅ Ri ⋙ Rf') (M : 𝒟₁) (K' : 𝒟₂)
    (α : Lf.obj M ⟶ Li.obj K') : Rj.obj M ⊞ Rf'.obj K' ⟶ Rj.obj (Rf.obj (Li.obj K')) :=
  biprod.desc (Rj.map (adjF.homEquiv M (Li.obj K') α))
    (-(Rf'.map (adjI.unit.app K') ≫ c.inv.app (Li.obj K')))

variable (adjF : Lf ⊣ Rf) (adjI : Li ⊣ Ri) (c : Rf ⋙ Rj ≅ Ri ⋙ Rf')

/-- The first component of the glueing map. -/
@[reassoc (attr := simp)]
theorem inl_glueingMap (M : 𝒟₁) (K' : 𝒟₂) (α : Lf.obj M ⟶ Li.obj K') :
    biprod.inl ≫ glueingMap adjF adjI c M K' α = Rj.map (adjF.homEquiv M (Li.obj K') α) :=
  biprod.inl_desc _ _

/-- The second component of the glueing map. -/
@[reassoc (attr := simp)]
theorem inr_glueingMap (M : 𝒟₁) (K' : 𝒟₂) (α : Lf.obj M ⟶ Li.obj K') :
    biprod.inr ≫ glueingMap adjF adjI c M K' α =
      -(Rf'.map (adjI.unit.app K') ≫ c.inv.app (Li.obj K')) :=
  biprod.inr_desc _ _

/-- **The glueing map is natural in `(M, K', α)`.** -/
theorem biprod_map_comp_glueingMap {M₁ M₂ : 𝒟₁} {K₁ K₂ : 𝒟₂} (m : M₁ ⟶ M₂) (k : K₁ ⟶ K₂)
    (α₁ : Lf.obj M₁ ⟶ Li.obj K₁) (α₂ : Lf.obj M₂ ⟶ Li.obj K₂)
    (h : Lf.map m ≫ α₂ = α₁ ≫ Li.map k) :
    biprod.map (Rj.map m) (Rf'.map k) ≫ glueingMap adjF adjI c M₂ K₂ α₂ =
      glueingMap adjF adjI c M₁ K₁ α₁ ≫ Rj.map (Rf.map (Li.map k)) := by
  apply biprod.hom_ext'
  · rw [biprod.inl_map_assoc, inl_glueingMap, inl_glueingMap_assoc, ← Rj.map_comp,
      ← Rj.map_comp, ← Adjunction.homEquiv_naturality_left, h,
      Adjunction.homEquiv_naturality_right]
  · rw [biprod.inr_map_assoc, inr_glueingMap, inr_glueingMap_assoc, Preadditive.comp_neg,
      Preadditive.neg_comp, Category.assoc]
    congr 1
    have hc := c.inv.naturality (Li.map k)
    dsimp at hc
    rw [← hc, ← Rf'.map_comp_assoc, ← Rf'.map_comp_assoc, Adjunction.unit_naturality]

/-- **Changing the adjunctions.** Let `adjF₀ : Lf₀ ⊣ Rf` and `adjI₀ : Li₀ ⊣ Ri` be two further
adjunctions with the same right adjoints. The glueing map for `adjF` and `adjI`, followed by the
comparison `Li K' ≅ Li₀ K'` of the two left adjoints, is the glueing map for `adjF₀` and `adjI₀`
of the corresponding map `Lf₀ M ⟶ Li₀ K'`. -/
theorem glueingMap_comp_leftAdjointUniq {Lf₀ : 𝒟₁ ⥤ 𝒟₀} {Li₀ : 𝒟₂ ⥤ 𝒟₀} (adjF₀ : Lf₀ ⊣ Rf)
    (adjI₀ : Li₀ ⊣ Ri) (M : 𝒟₁) (K' : 𝒟₂) (α : Lf.obj M ⟶ Li.obj K') :
    glueingMap adjF adjI c M K' α ≫ Rj.map (Rf.map ((adjI.leftAdjointUniq adjI₀).hom.app K')) =
      glueingMap adjF₀ adjI₀ c M K'
        ((adjF.leftAdjointUniq adjF₀).inv.app M ≫ α ≫ (adjI.leftAdjointUniq adjI₀).hom.app K') := by
  apply biprod.hom_ext'
  · rw [inl_glueingMap_assoc, inl_glueingMap, ← Rj.map_comp,
      ← Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    simp only [Functor.map_comp, Adjunction.leftAdjointUniq_inv_app,
      Adjunction.unit_leftAdjointUniq_hom_app_assoc]
  · rw [inr_glueingMap_assoc, inr_glueingMap, Preadditive.neg_comp, Category.assoc]
    congr 1
    have hc := c.inv.naturality ((adjI.leftAdjointUniq adjI₀).hom.app K')
    dsimp at hc
    rw [← hc, ← Rf'.map_comp_assoc, Adjunction.unit_leftAdjointUniq_hom_app]

/-- **Replacing the right adjoints by isomorphic functors.** Let `eJ`, `eF'`, `eF`, `eI` be
isomorphisms from `Rj`, `Rf'`, `Rf`, `Ri` to `Rj₀`, `Rf'₀`, `Rf₀`, `Ri₀`, and let
`c₀ : Rf₀ ⋙ Rj₀ ≅ Ri₀ ⋙ Rf'₀` correspond to `c` under them. Then the glueing map for `adjF` and
`adjI` corresponds to the glueing map for the transported adjunctions. -/
theorem glueingMap_comp_ofNatIsoRight {Rj₀ : 𝒟₁ ⥤ 𝒟} {Rf'₀ : 𝒟₂ ⥤ 𝒟} {Rf₀ : 𝒟₀ ⥤ 𝒟₁}
    {Ri₀ : 𝒟₀ ⥤ 𝒟₂} (eJ : Rj ≅ Rj₀) (eF' : Rf' ≅ Rf'₀) (eF : Rf ≅ Rf₀) (eI : Ri ≅ Ri₀)
    (c₀ : Rf₀ ⋙ Rj₀ ≅ Ri₀ ⋙ Rf'₀)
    (hc : ∀ X : 𝒟₀, c.hom.app X ≫ eF'.hom.app (Ri.obj X) ≫ Rf'₀.map (eI.hom.app X) =
      eJ.hom.app (Rf.obj X) ≫ Rj₀.map (eF.hom.app X) ≫ c₀.hom.app X)
    (M : 𝒟₁) (K' : 𝒟₂) (α : Lf.obj M ⟶ Li.obj K') :
    glueingMap adjF adjI c M K' α ≫ eJ.hom.app (Rf.obj (Li.obj K')) ≫
        Rj₀.map (eF.hom.app (Li.obj K')) =
      biprod.map (eJ.hom.app M) (eF'.hom.app K') ≫
        glueingMap (adjF.ofNatIsoRight eF) (adjI.ofNatIsoRight eI) c₀ M K' α := by
  apply biprod.hom_ext'
  · rw [inl_glueingMap_assoc, biprod.inl_map_assoc, inl_glueingMap,
      Adjunction.homEquiv_ofNatIsoRight_apply, Rj₀.map_comp, ← eJ.hom.naturality_assoc]
  · rw [inr_glueingMap_assoc, biprod.inr_map_assoc, inr_glueingMap, Preadditive.neg_comp,
      Preadditive.comp_neg, Category.assoc]
    congr 1
    have h := hc (Li.obj K')
    have h' : c.inv.app (Li.obj K') ≫ eJ.hom.app (Rf.obj (Li.obj K')) ≫
        Rj₀.map (eF.hom.app (Li.obj K')) =
        eF'.hom.app (Ri.obj (Li.obj K')) ≫ Rf'₀.map (eI.hom.app (Li.obj K')) ≫
          c₀.inv.app (Li.obj K') := by
      rw [← cancel_epi (c.hom.app (Li.obj K')), Iso.hom_inv_id_app_assoc, reassoc_of% h]
      simp
    have hu : (adjI.ofNatIsoRight eI).unit.app K' = adjI.unit.app K' ≫ eI.hom.app (Li.obj K') := by
      rw [← Adjunction.homEquiv_id, ← Adjunction.homEquiv_id,
        Adjunction.homEquiv_ofNatIsoRight_apply]
    rw [h', eF'.hom.naturality_assoc, hu, Rf'₀.map_comp, Category.assoc]

/-- Two adjunctions with the same right adjoint have adjoint transposes differing by the
comparison of their left adjoints. -/
theorem homEquiv_symm_eq_leftAdjointUniq_hom_app_comp {Lf₀ : 𝒟₁ ⥤ 𝒟₀} (adjF₀ : Lf₀ ⊣ Rf)
    {M : 𝒟₁} {X : 𝒟₀} (g : M ⟶ Rf.obj X) :
    (adjF.homEquiv M X).symm g =
      (adjF.leftAdjointUniq adjF₀).hom.app M ≫ (adjF₀.homEquiv M X).symm g := by
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, ← Category.assoc,
    ← (adjF.leftAdjointUniq adjF₀).hom.naturality g, Category.assoc,
    Adjunction.leftAdjointUniq_hom_app_counit]

variable {Lj : 𝒟 ⥤ 𝒟₁} {Lf' : 𝒟 ⥤ 𝒟₂} (adjJ : Lj ⊣ Rj) (adjF' : Lf' ⊣ Rf')

/-- **The identification `Rf ⋙ Rj ≅ Ri ⋙ Rf'` of the proof of Stacks 0DL7**: the conjugate,
under the composite adjunctions `Lj ⋙ Lf ⊣ Rf ⋙ Rj` and `Lf' ⋙ Li ⊣ Ri ⋙ Rf'`, of a 2-cell
`σ : Lj ⋙ Lf ≅ Lf' ⋙ Li`. -/
def glueingConjugateIso (σ : Lj ⋙ Lf ≅ Lf' ⋙ Li) : Rf ⋙ Rj ≅ Ri ⋙ Rf' :=
  conjugateIsoEquiv (adjJ.comp adjF) (adjF'.comp adjI) σ.symm

omit [Preadditive 𝒟] [HasBinaryBiproducts 𝒟] in
/-- The unit of `Lj ⋙ Lf ⊣ Rf ⋙ Rj` followed by `Rf ⋙ Rj` of the 2-cell is the unit of
`Lf' ⋙ Li ⊣ Ri ⋙ Rf'` followed by the inverse of the conjugate identification. -/
theorem comp_unit_app_comp_map_hom_app_eq (σ : Lj ⋙ Lf ≅ Lf' ⋙ Li) (M' : 𝒟) :
    (adjJ.comp adjF).unit.app M' ≫ Rj.map (Rf.map (σ.hom.app M')) =
      (adjF'.comp adjI).unit.app M' ≫
        (glueingConjugateIso adjF adjI adjJ adjF' σ).inv.app (Li.obj (Lf'.obj M')) := by
  set c := glueingConjugateIso adjF adjI adjJ adjF' σ
  have key : (adjJ.comp adjF).unit.app M' ≫ Rj.map (Rf.map (σ.hom.app M')) ≫
      c.hom.app (Li.obj (Lf'.obj M')) = (adjF'.comp adjI).unit.app M' := by
    have h₁ := c.hom.naturality (σ.hom.app M')
    have h₂ := unit_conjugateEquiv (adjJ.comp adjF) (adjF'.comp adjI) σ.inv M'
    dsimp only [Functor.comp_map, Functor.comp_obj] at h₁ h₂ ⊢
    rw [h₁, ← Category.assoc]
    show ((adjJ.comp adjF).unit.app M' ≫
      (conjugateEquiv (adjJ.comp adjF) (adjF'.comp adjI) σ.inv).app (Lf.obj (Lj.obj M'))) ≫ _ = _
    rw [h₂, Category.assoc, ← Functor.map_comp, ← Functor.map_comp, Iso.inv_hom_id_app]
    simp
  rw [← key]
  simp

/-- **The maps of the proof of Stacks 0DL7 are compatible with `α`.** Let
`σ : Lj ⋙ Lf ≅ Lf' ⋙ Li` be a 2-cell, `c` its conjugate
(`MilnorPatching.glueingConjugateIso`), and let `u : M' ⟶ Rj M ⊞ Rf' K'` be killed by the glueing
map of `(M, K', α)`. Then the maps `a : Lj M' ⟶ M` and `b : Lf' M' ⟶ K'` adjoint to the two
components of `u` satisfy `σ ≫ Li b = Lf a ≫ α`: the triple `(M', a, b)` is a morphism, in the
2-fibre product, from the image of `M'` to `(M, K', α)`. -/
theorem hom_app_comp_map_homEquiv_symm_snd_eq (σ : Lj ⋙ Lf ≅ Lf' ⋙ Li) {M : 𝒟₁} {K' : 𝒟₂}
    (α : Lf.obj M ⟶ Li.obj K') {M' : 𝒟} (u : M' ⟶ Rj.obj M ⊞ Rf'.obj K')
    (hu : u ≫ glueingMap adjF adjI (glueingConjugateIso adjF adjI adjJ adjF' σ) M K' α = 0) :
    σ.hom.app M' ≫ Li.map ((adjF'.homEquiv _ _).symm (u ≫ biprod.snd)) =
      Lf.map ((adjJ.homEquiv _ _).symm (u ≫ biprod.fst)) ≫ α := by
  set c := glueingConjugateIso adjF adjI adjJ adjF' σ
  apply ((adjJ.comp adjF).homEquiv _ _).injective
  have hrhs : (adjJ.comp adjF).homEquiv _ _
      (Lf.map ((adjJ.homEquiv _ _).symm (u ≫ biprod.fst)) ≫ α) =
      (u ≫ biprod.fst) ≫ Rj.map (adjF.homEquiv _ _ α) := by
    rw [Adjunction.comp_homEquiv, Equiv.trans_apply, Adjunction.homEquiv_naturality_left,
      Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
  have hlhs : (adjJ.comp adjF).homEquiv _ _
      (σ.hom.app M' ≫ Li.map ((adjF'.homEquiv _ _).symm (u ≫ biprod.snd))) =
      (u ≫ biprod.snd) ≫ Rf'.map (adjI.unit.app K') ≫ c.inv.app (Li.obj K') := by
    rw [Adjunction.homEquiv_unit]
    dsimp only [Functor.comp_map]
    rw [Functor.map_comp, Functor.map_comp,
      reassoc_of% comp_unit_app_comp_map_hom_app_eq adjF adjI adjJ adjF']
    have hn := c.inv.naturality (Li.map ((adjF'.homEquiv _ _).symm (u ≫ biprod.snd)))
    dsimp only [Functor.comp_map, Functor.comp_obj] at hn
    rw [← hn]
    have h₂ : (adjF'.comp adjI).unit.app M' ≫
        Rf'.map (Ri.map (Li.map ((adjF'.homEquiv _ _).symm (u ≫ biprod.snd)))) =
        (u ≫ biprod.snd) ≫ Rf'.map (adjI.unit.app K') := by
      have := ((adjF'.comp adjI).homEquiv_unit M' (Li.obj K')
        (Li.map ((adjF'.homEquiv _ _).symm (u ≫ biprod.snd)))).symm
      dsimp only [Functor.comp_map] at this
      have h₃ : adjI.homEquiv _ _ (Li.map ((adjF'.homEquiv _ _).symm (u ≫ biprod.snd))) =
          (adjF'.homEquiv _ _).symm (u ≫ biprod.snd) ≫ adjI.unit.app K' := by
        rw [Adjunction.homEquiv_unit, Adjunction.unit_naturality]
      rw [this, Adjunction.comp_homEquiv, Equiv.trans_apply, h₃,
        Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
    rw [reassoc_of% h₂]
    simp only [Category.assoc]
  rw [hrhs, hlhs]
  have h := hu
  rw [glueingMap, biprod.desc_eq, Preadditive.comp_add, Preadditive.comp_neg,
    Preadditive.comp_neg, ← sub_eq_add_neg, sub_eq_zero] at h
  simp only [Category.assoc]
  exact h.symm

/-- **Twisting the identification by an automorphism of the identity.** If `c'` differs from `c` by
an automorphism `ν` of the identity functor of `𝒟₀` (for instance multiplication by a unit, when
`𝒟₀` is a derived category of modules), the glueing map for `c'` and `α` is the glueing map for
`c` and `α ≫ ν` followed by the isomorphism `Rj Rf ν⁻¹`. -/
theorem glueingMap_eq_of_hom_app_eq (c' : Rf ⋙ Rj ≅ Ri ⋙ Rf') (ν : 𝟭 𝒟₀ ≅ 𝟭 𝒟₀)
    (h : ∀ X : 𝒟₀, c'.hom.app X = Rj.map (Rf.map (ν.hom.app X)) ≫ c.hom.app X)
    (M : 𝒟₁) (K' : 𝒟₂) (α : Lf.obj M ⟶ Li.obj K') :
    glueingMap adjF adjI c' M K' α =
      glueingMap adjF adjI c M K' (α ≫ ν.hom.app (Li.obj K')) ≫
        Rj.map (Rf.map (ν.inv.app (Li.obj K'))) := by
  have hinv : c'.inv.app (Li.obj K') =
      c.inv.app (Li.obj K') ≫ Rj.map (Rf.map (ν.inv.app (Li.obj K'))) := by
    rw [← cancel_epi (c'.hom.app (Li.obj K')), Iso.hom_inv_id_app, h, Category.assoc,
      Iso.hom_inv_id_app_assoc, ← Functor.map_comp, ← Functor.map_comp, Iso.hom_inv_id_app]
    simp
  apply biprod.hom_ext'
  · rw [inl_glueingMap, inl_glueingMap_assoc, ← Rj.map_comp,
      Adjunction.homEquiv_naturality_right, Category.assoc, ← Rf.map_comp, Iso.hom_inv_id_app]
    simp
  · rw [inr_glueingMap, inr_glueingMap_assoc, hinv, Preadditive.neg_comp, Category.assoc]

end Generic

section FibreProduct

variable {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
  {toBase : B →+* A} {surjection : A' →+* A} (I : Ideal A')
  (s : RingFibreProduct.Situation toBase surjection I)

/-- The two maps `B' → A` through `B` and through `A'` agree. -/
theorem toBase_comp_fibreProductFst :
    toBase.comp (fibreProductFst I s) = fibreProductToBase I s :=
  RingHom.ext (fibreProduct_toBase_fst I s)

variable [HasDerivedCategory.{w₁} (ModuleCat.{u} s.fibreProduct)]
  [HasDerivedCategory.{w₂} (ModuleCat.{u} B)] [HasDerivedCategory.{w₃} (ModuleCat.{u} A')]
  [HasDerivedCategory.{w₄} (ModuleCat.{u} A)]

/-- Derived restriction of scalars `D(B) ⥤ D(B')` along `B' → B`, the `Rj_*` of the lemma. -/
abbrev derivedRestrictFst :
    DerivedCategory (ModuleCat.{u} B) ⥤ DerivedCategory (ModuleCat.{u} s.fibreProduct) :=
  (ModuleCat.restrictScalars.{u} (fibreProductFst I s)).mapDerivedCategory

/-- Derived restriction of scalars `D(A') ⥤ D(B')` along `B' → A'`, the `Rf'_*` of the lemma. -/
abbrev derivedRestrictSnd :
    DerivedCategory (ModuleCat.{u} A') ⥤ DerivedCategory (ModuleCat.{u} s.fibreProduct) :=
  (ModuleCat.restrictScalars.{u} (fibreProductSnd I s)).mapDerivedCategory

/-- Derived restriction of scalars `D(A) ⥤ D(B')` along `B' → A`. -/
abbrev derivedRestrictToBase :
    DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} s.fibreProduct) :=
  (ModuleCat.restrictScalars.{u} (fibreProductToBase I s)).mapDerivedCategory

/-- Derived restriction of scalars along `B' → B → A` is derived restriction along `B' → A`. -/
def derivedRestrictFstCompIso :
    (ModuleCat.restrictScalars.{u} toBase).mapDerivedCategory ⋙ derivedRestrictFst I s ≅
      derivedRestrictToBase I s :=
  Dualizing.mapDerivedCategoryCompNatIso (ModuleCat.restrictScalars.{u} toBase)
    (ModuleCat.restrictScalars.{u} (fibreProductFst I s))
    (ModuleCat.restrictScalars.{u} (fibreProductToBase I s))
    (ModuleCat.restrictScalarsComp'.{u} (fibreProductFst I s) toBase (fibreProductToBase I s)
      (toBase_comp_fibreProductFst I s).symm).symm

/-- Derived restriction of scalars along `B' → A' → A` is derived restriction along `B' → A`. -/
def derivedRestrictSndCompIso :
    (ModuleCat.restrictScalars.{u} surjection).mapDerivedCategory ⋙ derivedRestrictSnd I s ≅
      derivedRestrictToBase I s :=
  Dualizing.mapDerivedCategoryCompNatIso (ModuleCat.restrictScalars.{u} surjection)
    (ModuleCat.restrictScalars.{u} (fibreProductSnd I s))
    (ModuleCat.restrictScalars.{u} (fibreProductToBase I s))
    (ModuleCat.restrictScalarsComp'.{u} (fibreProductSnd I s) surjection (fibreProductToBase I s)
      rfl).symm

/-- **The identification `Rj_* Rf_* = Rf'_* Ri_*`** of the lemma: derived restriction of scalars
along `B' → B → A` and along `B' → A' → A` agree. -/
def derivedRestrictCompIso :
    (ModuleCat.restrictScalars.{u} toBase).mapDerivedCategory ⋙ derivedRestrictFst I s ≅
      (ModuleCat.restrictScalars.{u} surjection).mapDerivedCategory ⋙ derivedRestrictSnd I s :=
  derivedRestrictFstCompIso I s ≪≫ (derivedRestrictSndCompIso I s).symm

variable (E : CochainComplex (ModuleCat.{u} B) ℤ) (P : CochainComplex (ModuleCat.{u} A') ℤ)
  (φ : ((ModuleCat.extendScalars.{u, u, u} toBase).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj E ≅
    ((ModuleCat.extendScalars.{u, u, u} surjection).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P)
  (hE : ∀ n, Module.Finite B (E.X n) ∧ Module.Projective B (E.X n))
  (hP : ∀ n, Module.Finite A' (P.X n) ∧ Module.Projective A' (P.X n))
  (G₁ : DerivedCategory (ModuleCat.{u} B) ⥤ DerivedCategory (ModuleCat.{u} A))
  (β₁ : DerivedCategory.Q ⋙ G₁ ⟶
    (ModuleCat.extendScalars.{u, u, u} toBase).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q)
  [G₁.IsLeftDerivedFunctor β₁ (HomologicalComplex.quasiIso (ModuleCat.{u} B) (ComplexShape.up ℤ))]
  (G₂ : DerivedCategory (ModuleCat.{u} A') ⥤ DerivedCategory (ModuleCat.{u} A))
  (β₂ : DerivedCategory.Q ⋙ G₂ ⟶
    (ModuleCat.extendScalars.{u, u, u} surjection).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q)
  [G₂.IsLeftDerivedFunctor β₂
    (HomologicalComplex.quasiIso (ModuleCat.{u} A') (ComplexShape.up ℤ))]

/-- **The isomorphism `E ⊗ᴸ_B A ≅ P ⊗ᴸ_{A'} A` represented by `φ`**, where the derived extensions
of scalars are computed degreewise at `E` and at `P`. -/
def complexDerivedExtensionIso [IsIso (β₁.app E)] [IsIso (β₂.app P)] :
    G₁.obj (DerivedCategory.Q.obj E) ≅ G₂.obj (DerivedCategory.Q.obj P) :=
  asIso (β₁.app E) ≪≫ DerivedCategory.Q.mapIso φ ≪≫ (asIso (β₂.app P)).symm

omit [G₁.IsLeftDerivedFunctor β₁
      (HomologicalComplex.quasiIso (ModuleCat.{u} B) (ComplexShape.up ℤ))]
    [G₂.IsLeftDerivedFunctor β₂
      (HomologicalComplex.quasiIso (ModuleCat.{u} A') (ComplexShape.up ℤ))] in
/-- `complexDerivedExtensionIso` followed by the comparison at `P` is the comparison at `E`
followed by `φ`. -/
@[reassoc]
theorem complexDerivedExtensionIso_hom_comp [IsIso (β₁.app E)] [IsIso (β₂.app P)] :
    (complexDerivedExtensionIso E P φ G₁ β₁ G₂ β₂).hom ≫ β₂.app P =
      β₁.app E ≫ DerivedCategory.Q.map φ.hom := by
  simp [complexDerivedExtensionIso]

/-- The identification of the source `Rj_* E ⊕ Rf'_* P` of the glueing map with the localization
of the direct sum of `E` and `P`, read as complexes of `B'`-modules. -/
def glueingSourceIso :
    (derivedRestrictFst I s).obj (DerivedCategory.Q.obj E) ⊞
        (derivedRestrictSnd I s).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj (restrictedFst I s E ⊞ restrictedSnd I s P) :=
  haveI : PreservesBinaryBiproducts
      (DerivedCategory.Q (C := ModuleCat.{u} s.fibreProduct)) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  biprod.mapIso
      ((ModuleCat.restrictScalars.{u} (fibreProductFst I s)).mapDerivedCategoryFactors.app E)
      ((ModuleCat.restrictScalars.{u} (fibreProductSnd I s)).mapDerivedCategoryFactors.app P) ≪≫
    (DerivedCategory.Q.mapBiprod (restrictedFst I s E) (restrictedSnd I s P)).symm

omit [HasDerivedCategory.{w₄} (ModuleCat.{u} A)] in
  /-- The first inclusion followed by `glueingSourceIso` and the localization of a map out of the
  direct sum. -/
  private theorem inl_glueingSourceIso_hom_comp_map
    {Z : CochainComplex (ModuleCat.{u} s.fibreProduct) ℤ}
    (h : restrictedFst I s E ⊞ restrictedSnd I s P ⟶ Z) :
    biprod.inl ≫ (glueingSourceIso I s E P).hom ≫ DerivedCategory.Q.map h =
      (ModuleCat.restrictScalars.{u} (fibreProductFst I s)).mapDerivedCategoryFactors.hom.app E ≫
        DerivedCategory.Q.map (biprod.inl ≫ h) := by
  simp only [glueingSourceIso, Iso.trans_hom, Iso.symm_hom, biprod.mapIso_hom,
    Functor.mapBiprod_inv, Category.assoc, biprod.inl_map_assoc, biprod.inl_desc_assoc,
    ← Functor.map_comp, Iso.app_hom]

omit [HasDerivedCategory.{w₄} (ModuleCat.{u} A)] in
  /-- The second inclusion followed by `glueingSourceIso` and the localization of a map out of the
  direct sum. -/
  private theorem inr_glueingSourceIso_hom_comp_map
    {Z : CochainComplex (ModuleCat.{u} s.fibreProduct) ℤ}
    (h : restrictedFst I s E ⊞ restrictedSnd I s P ⟶ Z) :
    biprod.inr ≫ (glueingSourceIso I s E P).hom ≫ DerivedCategory.Q.map h =
      (ModuleCat.restrictScalars.{u} (fibreProductSnd I s)).mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map (biprod.inr ≫ h) := by
  simp only [glueingSourceIso, Iso.trans_hom, Iso.symm_hom, biprod.mapIso_hom,
    Functor.mapBiprod_inv, Category.assoc, biprod.inr_map_assoc, biprod.inr_desc_assoc,
    ← Functor.map_comp, Iso.app_hom]

omit [HasDerivedCategory.{w₄} (ModuleCat.{u} A)] in
/-- `glueingSourceIso` on the first summand. -/
@[reassoc]
theorem glueingSourceIso_hom_fst :
    (glueingSourceIso I s E P).hom ≫ DerivedCategory.Q.map biprod.fst =
      biprod.fst ≫ (ModuleCat.restrictScalars.{u}
        (fibreProductFst I s)).mapDerivedCategoryFactors.hom.app E := by
  apply biprod.hom_ext'
  · rw [inl_glueingSourceIso_hom_comp_map]; simp
  · rw [inr_glueingSourceIso_hom_comp_map]; simp

omit [HasDerivedCategory.{w₄} (ModuleCat.{u} A)] in
/-- `glueingSourceIso` on the second summand. -/
@[reassoc]
theorem glueingSourceIso_hom_snd :
    (glueingSourceIso I s E P).hom ≫ DerivedCategory.Q.map biprod.snd =
      biprod.snd ≫ (ModuleCat.restrictScalars.{u}
        (fibreProductSnd I s)).mapDerivedCategoryFactors.hom.app P := by
  apply biprod.hom_ext'
  · rw [inl_glueingSourceIso_hom_comp_map]; simp
  · rw [inr_glueingSourceIso_hom_comp_map]; simp

/-- The identification of the target `Rj_* Rf_* (P ⊗ᴸ_{A'} A)` of the glueing map with the
localization of `P ⊗_{A'} A`, read as a complex of `B'`-modules. -/
def glueingTargetIso [IsIso (β₂.app P)] :
    (derivedRestrictFst I s).obj ((ModuleCat.restrictScalars.{u} toBase).mapDerivedCategory.obj
        (G₂.obj (DerivedCategory.Q.obj P))) ≅
      DerivedCategory.Q.obj (restrictedBase I s P) :=
  ((ModuleCat.restrictScalars.{u} toBase).mapDerivedCategory ⋙ derivedRestrictFst I s).mapIso
      (asIso (β₂.app P)) ≪≫
    (derivedRestrictFstCompIso I s).app (DerivedCategory.Q.obj
      (((ModuleCat.extendScalars.{u, u, u} surjection).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P)) ≪≫
    (ModuleCat.restrictScalars.{u} (fibreProductToBase I s)).mapDerivedCategoryFactors.app
      (((ModuleCat.extendScalars.{u, u, u} surjection).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P)

omit [HasDerivedCategory.{w₁} (ModuleCat.{u} s.fibreProduct)]
    [HasDerivedCategory.{w₂} (ModuleCat.{u} B)] [HasDerivedCategory.{w₃} (ModuleCat.{u} A')]
    [HasDerivedCategory.{w₄} (ModuleCat.{u} A)] in
/-- `compatibleFstMap` is degreewise restriction of scalars of the unit followed by `φ`. -/
theorem compatibleFstMap_eq :
    compatibleFstMap I s E P φ =
      ((ModuleCat.restrictScalars.{u} (fibreProductFst I s)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
        (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} toBase).mapHomologicalComplex
            (ComplexShape.up ℤ)).unit.app E ≫
          ((ModuleCat.restrictScalars.{u} toBase).mapHomologicalComplex (ComplexShape.up ℤ)).map
            φ.hom) ≫
        (Functor.mapHomologicalComplexCompIso
          (ModuleCat.restrictScalarsComp'.{u} (fibreProductFst I s) toBase
            (fibreProductToBase I s) (toBase_comp_fibreProductFst I s).symm).symm
          (ComplexShape.up ℤ)).hom.app _ := by
  ext n : 1
  rfl

omit [HasDerivedCategory.{w₁} (ModuleCat.{u} s.fibreProduct)]
    [HasDerivedCategory.{w₂} (ModuleCat.{u} B)] [HasDerivedCategory.{w₃} (ModuleCat.{u} A')]
    [HasDerivedCategory.{w₄} (ModuleCat.{u} A)] in
/-- `compatibleSndMap` is degreewise restriction of scalars of the unit. -/
theorem compatibleSndMap_eq :
    compatibleSndMap I s P =
      ((ModuleCat.restrictScalars.{u} (fibreProductSnd I s)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
        (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} surjection).mapHomologicalComplex
            (ComplexShape.up ℤ)).unit.app P) ≫
        (Functor.mapHomologicalComplexCompIso
          (ModuleCat.restrictScalarsComp'.{u} (fibreProductSnd I s) surjection
            (fibreProductToBase I s) rfl).symm
          (ComplexShape.up ℤ)).hom.app _ := by
  ext n : 1
  rfl

/-- **The glueing map is the second map of the patched short exact sequence.** For derived
restriction of scalars along the maps of the fibre product `B' = B ×_A A'`, the derived
change-of-rings adjunctions along `B → A` and `A' → A`, and the isomorphism
`E ⊗ᴸ_B A ≅ P ⊗ᴸ_{A'} A` represented by `φ`, the glueing map
`Rj_* E ⊕ Rf'_* P ⟶ Rj_* Rf_* (P ⊗ᴸ_{A'} A)` is, under `glueingSourceIso` and
`glueingTargetIso`, the map `(e, p) ↦ φ (1 ⊗ e) - 1 ⊗ p` of `patchedShortComplex`. -/
theorem glueingMap_comp_glueingTargetIso [IsIso (β₁.app E)] [IsIso (β₂.app P)] :
    glueingMap
        (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, u}
          toBase G₁ β₁)
        (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, u}
          surjection G₂ β₂)
        (derivedRestrictCompIso I s) (DerivedCategory.Q.obj E) (DerivedCategory.Q.obj P)
        (complexDerivedExtensionIso E P φ G₁ β₁ G₂ β₂).hom ≫
      (glueingTargetIso I s P G₂ β₂).hom =
    (glueingSourceIso I s E P).hom ≫
      DerivedCategory.Q.map
        (biprod.desc (compatibleFstMap I s E P φ) (-compatibleSndMap I s P)) := by
  let : (ModuleCat.extendScalars.{u, u, u} toBase).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} toBase).left_adjoint_additive
  let : (ModuleCat.extendScalars.{u, u, u} surjection).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} surjection).left_adjoint_additive
  let RF := ModuleCat.restrictScalars.{u} toBase
  let RI := ModuleCat.restrictScalars.{u} surjection
  let RJ := ModuleCat.restrictScalars.{u} (fibreProductFst I s)
  let RF' := ModuleCat.restrictScalars.{u} (fibreProductSnd I s)
  let RH := ModuleCat.restrictScalars.{u} (fibreProductToBase I s)
  let EA := ((ModuleCat.extendScalars.{u, u, u} toBase).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj E
  let PA := ((ModuleCat.extendScalars.{u, u, u} surjection).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj P
  have hunitF := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_unit_app
    toBase G₁ β₁ E
  have hunitI := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_unit_app
    surjection G₂ β₂ P
  have hΦ₁ := Dualizing.mapDerivedCategoryCompNatIso_hom_app_Q RF RJ RH
    (ModuleCat.restrictScalarsComp'.{u} (fibreProductFst I s) toBase (fibreProductToBase I s)
      (toBase_comp_fibreProductFst I s).symm).symm PA
  have hΦ₂ := Dualizing.mapDerivedCategoryCompNatIso_hom_app_Q RI RF' RH
    (ModuleCat.restrictScalarsComp'.{u} (fibreProductSnd I s) surjection (fibreProductToBase I s)
      rfl).symm PA
  have hα := complexDerivedExtensionIso_hom_comp E P φ G₁ β₁ G₂ β₂
  let RFd := RF.mapDerivedCategory
  let RJd := RJ.mapDerivedCategory
  let RF'd := RF'.mapDerivedCategory
  let RId := RI.mapDerivedCategory
  let RHd := RH.mapDerivedCategory
  let Φ₁ := derivedRestrictFstCompIso I s
  let Φ₂ := derivedRestrictSndCompIso I s
  have hΦ₁' : Φ₁.hom.app (DerivedCategory.Q.obj PA) = _ := hΦ₁
  have hΦ₂' : Φ₂.hom.app (DerivedCategory.Q.obj PA) = _ := hΦ₂
  have he₃ : (glueingTargetIso I s P G₂ β₂).hom =
      RJd.map (RFd.map (β₂.app P)) ≫ Φ₁.hom.app (DerivedCategory.Q.obj PA) ≫
        RH.mapDerivedCategoryFactors.hom.app PA := rfl
  apply biprod.hom_ext'
  · rw [inl_glueingMap_assoc, Adjunction.homEquiv_unit]
    have hR : biprod.inl ≫ (glueingSourceIso I s E P).hom ≫ DerivedCategory.Q.map
          (biprod.desc (compatibleFstMap I s E P φ) (-compatibleSndMap I s P)) =
        RJ.mapDerivedCategoryFactors.hom.app E ≫
          DerivedCategory.Q.map (compatibleFstMap I s E P φ) := by
      rw [inl_glueingSourceIso_hom_comp_map, biprod.inl_desc]
    have h1 : (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, u}
          toBase G₁ β₁).unit.app (DerivedCategory.Q.obj E) ≫
          RFd.map (complexDerivedExtensionIso E P φ G₁ β₁ G₂ β₂).hom ≫ RFd.map (β₂.app P) =
        DerivedCategory.Q.map (((ModuleCat.extendRestrictScalarsAdj.{u, u, u}
            toBase).mapHomologicalComplex (ComplexShape.up ℤ)).unit.app E) ≫
          RF.mapDerivedCategoryFactors.inv.app EA ≫ RFd.map (DerivedCategory.Q.map φ.hom) := by
      rw [← RFd.map_comp, hα, RFd.map_comp, reassoc_of% hunitF]
    have h3 : RF.mapDerivedCategoryFactors.inv.app EA ≫ RFd.map (DerivedCategory.Q.map φ.hom) ≫
          RF.mapDerivedCategoryFactors.hom.app PA =
        DerivedCategory.Q.map ((RF.mapHomologicalComplex (ComplexShape.up ℤ)).map φ.hom) := by
      rw [Functor.mapDerivedCategoryFactors_hom_naturality, Iso.inv_hom_id_app_assoc]
    rw [hR, he₃, hΦ₁', ← RJd.map_comp_assoc]
    simp only [Category.assoc]
    rw [h1, ← Functor.map_comp_assoc]
    simp only [Category.assoc]
    rw [h3, ← DerivedCategory.Q.map_comp,
      Functor.mapDerivedCategoryFactors_hom_naturality_assoc, Iso.inv_hom_id_app,
      compatibleFstMap_eq]
    simp only [Functor.comp_obj, Functor.id_obj, Category.comp_id, Functor.map_comp,
      Category.assoc]
    rfl
  · rw [inr_glueingMap_assoc]
    have hR : biprod.inr ≫ (glueingSourceIso I s E P).hom ≫ DerivedCategory.Q.map
          (biprod.desc (compatibleFstMap I s E P φ) (-compatibleSndMap I s P)) =
        -(RF'.mapDerivedCategoryFactors.hom.app P ≫
          DerivedCategory.Q.map (compatibleSndMap I s P)) := by
      rw [inr_glueingSourceIso_hom_comp_map, biprod.inr_desc, Functor.map_neg, Preadditive.comp_neg]
    have n₁ : Φ₁.inv.app (G₂.obj (DerivedCategory.Q.obj P)) ≫ RJd.map (RFd.map (β₂.app P)) =
        RHd.map (β₂.app P) ≫ Φ₁.inv.app (DerivedCategory.Q.obj PA) :=
      (Φ₁.inv.naturality (β₂.app P)).symm
    have n₂ : Φ₂.hom.app (G₂.obj (DerivedCategory.Q.obj P)) ≫ RHd.map (β₂.app P) =
        RF'd.map (RId.map (β₂.app P)) ≫ Φ₂.hom.app (DerivedCategory.Q.obj PA) :=
      (Φ₂.hom.naturality (β₂.app P)).symm
    have hc : (derivedRestrictCompIso I s).inv.app (G₂.obj (DerivedCategory.Q.obj P)) ≫
          (glueingTargetIso I s P G₂ β₂).hom =
        RF'd.map (RId.map (β₂.app P)) ≫ Φ₂.hom.app (DerivedCategory.Q.obj PA) ≫
          RH.mapDerivedCategoryFactors.hom.app PA := by
      have : (derivedRestrictCompIso I s).inv.app (G₂.obj (DerivedCategory.Q.obj P)) =
          Φ₂.hom.app (G₂.obj (DerivedCategory.Q.obj P)) ≫
            Φ₁.inv.app (G₂.obj (DerivedCategory.Q.obj P)) := rfl
      rw [this, he₃, Category.assoc, reassoc_of% n₁, Iso.inv_hom_id_app_assoc, reassoc_of% n₂]
    have hu : (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, u}
          surjection G₂ β₂).unit.app (DerivedCategory.Q.obj P) ≫ RId.map (β₂.app P) =
        DerivedCategory.Q.map (((ModuleCat.extendRestrictScalarsAdj.{u, u, u}
            surjection).mapHomologicalComplex (ComplexShape.up ℤ)).unit.app P) ≫
          RI.mapDerivedCategoryFactors.inv.app PA := hunitI
    rw [hR, Preadditive.neg_comp, Category.assoc, hc, ← Functor.map_comp_assoc, hu, hΦ₂']
    congr 1
    have e : DerivedCategory.Q.map (((ModuleCat.extendRestrictScalarsAdj.{u, u, u}
            surjection).mapHomologicalComplex (ComplexShape.up ℤ)).unit.app P) ≫
          RI.mapDerivedCategoryFactors.inv.app PA ≫ RI.mapDerivedCategoryFactors.hom.app PA =
        DerivedCategory.Q.map (((ModuleCat.extendRestrictScalarsAdj.{u, u, u}
            surjection).mapHomologicalComplex (ComplexShape.up ℤ)).unit.app P) := by
      rw [Iso.inv_hom_id_app]
      exact Category.comp_id _
    have n₃ : RF'd.map (DerivedCategory.Q.map (((ModuleCat.extendRestrictScalarsAdj.{u, u, u}
            surjection).mapHomologicalComplex (ComplexShape.up ℤ)).unit.app P)) ≫
          RF'.mapDerivedCategoryFactors.hom.app
            ((RI.mapHomologicalComplex (ComplexShape.up ℤ)).obj PA) =
        RF'.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map
          ((RF'.mapHomologicalComplex (ComplexShape.up ℤ)).map
            (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} surjection).mapHomologicalComplex
              (ComplexShape.up ℤ)).unit.app P)) :=
      Functor.mapDerivedCategoryFactors_hom_naturality _ _
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, Category.assoc, e, reassoc_of% n₃, Iso.inv_hom_id_app,
      compatibleSndMap_eq]
    simp only [Functor.comp_obj, Functor.id_obj, Category.comp_id, Functor.map_comp]
    rfl

/-- **The fibre of the glueing map is the patched complex.** A distinguished triangle
`M' → Rj_* E ⊕ Rf'_* P → Rj_* Rf_* (P ⊗ᴸ_{A'} A) → M'[1]` in `D(B')` whose second morphism is the
glueing map of `(E, P, φ)` has first vertex `L`: there is an isomorphism `M' ≅ L` under which
the first morphism is `L ⟶ E ⊕ P`. -/
theorem exists_iso_patchedComplex_of_distinguished_glueingMap [IsIso (β₁.app E)]
    [IsIso (β₂.app P)]
    (Tr : Pretriangulated.Triangle (DerivedCategory (ModuleCat.{u} s.fibreProduct)))
    (hTr : Tr ∈ distTriang (DerivedCategory (ModuleCat.{u} s.fibreProduct)))
    (e₂ : Tr.obj₂ ≅ (derivedRestrictFst I s).obj (DerivedCategory.Q.obj E) ⊞
      (derivedRestrictSnd I s).obj (DerivedCategory.Q.obj P))
    (e₃ : Tr.obj₃ ≅ (derivedRestrictFst I s).obj
      ((ModuleCat.restrictScalars.{u} toBase).mapDerivedCategory.obj
        (G₂.obj (DerivedCategory.Q.obj P))))
    (comm : Tr.mor₂ ≫ e₃.hom = e₂.hom ≫ glueingMap
        (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, u}
          toBase G₁ β₁)
        (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, u}
          surjection G₂ β₂)
        (derivedRestrictCompIso I s) (DerivedCategory.Q.obj E) (DerivedCategory.Q.obj P)
        (complexDerivedExtensionIso E P φ G₁ β₁ G₂ β₂).hom) :
    ∃ e₁ : Tr.obj₁ ≅ DerivedCategory.Q.obj (patchedComplex I s E P φ hE hP),
      Tr.mor₁ ≫ e₂.hom ≫ (glueingSourceIso I s E P).hom = e₁.hom ≫ DerivedCategory.Q.map
        (biprod.lift (patchedComplexToFst I s E P φ hE hP)
          (patchedComplexToSnd I s E P φ hE hP)) :=
  exists_iso_patchedComplex_of_distinguished I s E P φ hE hP Tr hTr
    (e₂ ≪≫ glueingSourceIso I s E P) (e₃ ≪≫ glueingTargetIso I s P G₂ β₂) (by
      rw [Iso.trans_hom, Iso.trans_hom, reassoc_of% comm, Category.assoc,
        glueingMap_comp_glueingTargetIso])

end FibreProduct

end MilnorPatching
