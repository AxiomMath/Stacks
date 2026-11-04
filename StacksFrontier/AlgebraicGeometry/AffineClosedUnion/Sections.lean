module

public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.AffineOpenHom
public import StacksFrontier.AlgebraicGeometry.AffineClosedUnion.Global

/-!
# Sections of a scheme covered by two closed subschemes meeting in the zero ideal sheaf

Let `X` be a scheme and `I₁`, `I₂` two quasi-coherent ideal sheaves on `X` with
`I₁ ⊓ I₂ = ⊥`, so that the scheme-theoretic union of the two closed subschemes they cut out is
the whole of `X`. `StacksDraft.AlgebraicGeometry.F3b.AffineClosedUnion.Global` proves that `X`
is then the *pushout* of `X(I₁) ← X(I₁ ⊔ I₂) → X(I₂)` in the category of all schemes. This file
reads that off on sections: for every open `V` of `X` the square

```
Γ(X, V) ----------> Γ(X(I₁), i₁⁻¹V)
   |                      |
   v                      v
Γ(X(I₂), i₂⁻¹V) --> Γ(X(I₁ ⊔ I₂), i⁻¹V)
```

is *cartesian*: a section of `𝒪_X` over `V` is the same thing as a pair of sections of the two
closed subschemes agreeing on their scheme-theoretic intersection.

This is the globalisation of the module-level content of
[Stacks, Tag 09NW](https://stacks.math.columbia.edu/tag/09NW) — in a reduced ring, ideals whose
zero loci cover the spectrum meet in zero, so `I → I·(A ⧸ J)` is bijective — to global sections
of the structure sheaf of an arbitrary scheme. Equivalently: `I₁` is carried isomorphically onto
its image in `𝒪_{X(I₂)}`, which on sections is the statement above.

## The two proofs

At `V = ⊤` the statement is *free* from the pushout: `AlgebraicGeometry.Scheme.Γ` is a right
adjoint (`AlgebraicGeometry.ΓSpec.adjunction`), so it turns the cocartesian square of schemes
into a cartesian square of rings. That is
`Stacks.AffineClosedUnion.isPullback_appTop_of_inf_eq_bot`, and its one-line proof is the whole
reason the pushout was worth proving.

For a general open `V` the same argument would need the pushout for the open subscheme `V`,
i.e. the pullback ideal sheaves `AlgebraicGeometry.Scheme.IdealSheafData.comap` and the
identification of `(I.comap V.ι).subscheme` with the preimage of `V` in `X(I)`. The route taken
here instead is elementary and affine-local, and it produces maps that are literally
`AlgebraicGeometry.Scheme.Hom.app`, which is what a consumer wants:

* over an **affine** open `U` the restriction `Γ(X, U) → Γ(X(I), i⁻¹U)` is surjective with kernel
  exactly `I.ideal U` (Mathlib's
  `AlgebraicGeometry.Scheme.IdealSheafData.subschemeι_app_surjective` and `ker_subschemeι_app`),
  so the square is the ring square `A → A⧸I, A → A⧸J` over `A⧸(I + J)`, cartesian because
  `I ⊓ J = ⊥` and `(I ⊔ J).ideal U` is `I.ideal U + J.ideal U`;
* the affine opens form a basis, so uniqueness globalises by the separatedness half of the sheaf
  condition and existence globalises by gluing.

No fibre product and no quasi-coherence is used; the only inputs are the two Mathlib facts above.

## Main definitions

* `Stacks.AffineClosedUnion.interRestrictLeft` and
  `Stacks.AffineClosedUnion.interRestrictRight`: the two restriction maps from the sections of
  `X(I₁)`, resp. `X(I₂)`, over the preimage of `V` to the sections of the scheme-theoretic
  intersection `X(I₁ ⊔ I₂)` over the preimage of `V`.

## Main results

* `Stacks.AffineClosedUnion.isPullback_appTop_of_inf_eq_bot`: the global sections of `X` are the
  fibre product of the global sections of the two closed subschemes over those of their
  intersection, as a cartesian square in `CommRingCat`.
* `Stacks.AffineClosedUnion.app_ext_of_inf_eq_bot`: a section of `𝒪_X` over any open is
  determined by its restrictions to the two closed subschemes.
* `Stacks.AffineClosedUnion.exists_app_eq_of_inf_eq_bot` and
  `Stacks.AffineClosedUnion.existsUnique_app_eq_of_inf_eq_bot`: a pair of sections of the two
  closed subschemes agreeing on the intersection extends, uniquely, to a section of `𝒪_X`.
* `Stacks.AffineClosedUnion.exists_app_eq_zero_of_inf_eq_bot`: the form used by
  [Stacks, Tag 09NX] — a section of `𝒪_{X(I₂)}` vanishing on the intersection is the restriction
  of a section of `𝒪_X` vanishing on `X(I₁)`.
* `Stacks.AffineClosedUnion.control_app_ext_without_inf_eq_bot_false`: the hypothesis
  `I₁ ⊓ I₂ = ⊥` is load-bearing for uniqueness — without it the statement is inconsistent.

## References

* [Stacks Project, Tag 09NW](https://stacks.math.columbia.edu/tag/09NW)
* [Stacks Project, Tag 09NX](https://stacks.math.columbia.edu/tag/09NX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.IdealSheafData

universe u

namespace Stacks.AffineClosedUnion

variable {X : Scheme.{u}}

/-- Restricting a section of `𝒪_X` and then pulling it back along a morphism is pulling it back
and then restricting. This is `AlgebraicGeometry.Scheme.Hom.naturality` read on elements. -/
theorem app_map {Y : Scheme.{u}} (f : Y ⟶ X) {U V : X.Opens} (i : U ⟶ V) (c : Γ(X, V)) :
    (f.app U).hom ((X.presheaf.map i.op).hom c)
      = (Y.presheaf.map ((Opens.map f.base).map i).op).hom ((f.app V).hom c) :=
  ConcreteCategory.congr_hom (Scheme.Hom.naturality f i.op) c

/-- Two composites of restriction maps between the same opens agree: the category of opens of a
scheme is thin. -/
theorem map_map_eq {Y : Scheme.{u}} {A B B' C : Y.Opens} (p : A ⟶ B) (q : B ⟶ C) (p' : A ⟶ B')
    (q' : B' ⟶ C) (t : Γ(Y, C)) :
    (Y.presheaf.map p.op).hom ((Y.presheaf.map q.op).hom t)
      = (Y.presheaf.map p'.op).hom ((Y.presheaf.map q'.op).hom t) := by
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

section Global

variable (I₁ I₂ : X.IdealSheafData)

/-- **The global sections of `X` are the fibre product of those of the two closed subschemes.**
If two quasi-coherent ideal sheaves meet in zero then `X` is the pushout of
`X(I₁) ← X(I₁ ⊔ I₂) → X(I₂)` in the category of schemes
(`Stacks.AffineClosedUnion.isPushout_subschemeι`), and `AlgebraicGeometry.Scheme.Γ` is a right
adjoint, so it carries that cocartesian square to a cartesian square of rings. -/
theorem isPullback_appTop_of_inf_eq_bot (h : I₁ ⊓ I₂ = ⊥) :
    IsPullback I₁.subschemeι.appTop I₂.subschemeι.appTop
      (inclusion (le_sup_left : I₁ ≤ I₁ ⊔ I₂)).appTop
      (inclusion (le_sup_right : I₂ ≤ I₁ ⊔ I₂)).appTop :=
  (((isPushout_subschemeι I₁ I₂ h).op).map Scheme.Γ).flip

/-- The global-sections square of `Stacks.AffineClosedUnion.isPullback_appTop_of_inf_eq_bot`,
read on elements: a pair of global sections of the two closed subschemes which agree on the
scheme-theoretic intersection comes from a global section of `X`. -/
theorem exists_appTop_eq_of_inf_eq_bot (h : I₁ ⊓ I₂ = ⊥) (a : Γ(I₁.subscheme, ⊤))
    (b : Γ(I₂.subscheme, ⊤))
    (hab : (inclusion (le_sup_left : I₁ ≤ I₁ ⊔ I₂)).appTop a =
      (inclusion (le_sup_right : I₂ ≤ I₁ ⊔ I₂)).appTop b) :
    ∃ c : Γ(X, ⊤), I₁.subschemeι.appTop c = a ∧ I₂.subschemeι.appTop c = b :=
  Types.exists_of_isPullback
    ((isPullback_appTop_of_inf_eq_bot I₁ I₂ h).map (CategoryTheory.forget CommRingCat.{u})) a b hab

end Global

section Restriction

variable (I₁ I₂ : X.IdealSheafData)

/-- The preimage of an open of `X` in the scheme-theoretic intersection, computed through the
first closed subscheme. -/
theorem inclusion_left_preimage (V : X.Opens) :
    (inclusion (le_sup_left : I₁ ≤ I₁ ⊔ I₂)) ⁻¹ᵁ (I₁.subschemeι ⁻¹ᵁ V)
      = (I₁ ⊔ I₂).subschemeι ⁻¹ᵁ V := by
  rw [← Scheme.Hom.comp_preimage, inclusion_subschemeι]

/-- The preimage of an open of `X` in the scheme-theoretic intersection, computed through the
second closed subscheme. -/
theorem inclusion_right_preimage (V : X.Opens) :
    (inclusion (le_sup_right : I₂ ≤ I₁ ⊔ I₂)) ⁻¹ᵁ (I₂.subschemeι ⁻¹ᵁ V)
      = (I₁ ⊔ I₂).subschemeι ⁻¹ᵁ V := by
  rw [← Scheme.Hom.comp_preimage, inclusion_subschemeι]

/-- Restriction of a section of the first closed subscheme to the scheme-theoretic
intersection. -/
noncomputable def interRestrictLeft (V : X.Opens) :
    Γ(I₁.subscheme, I₁.subschemeι ⁻¹ᵁ V) ⟶
      Γ((I₁ ⊔ I₂).subscheme, (I₁ ⊔ I₂).subschemeι ⁻¹ᵁ V) :=
  (inclusion (le_sup_left : I₁ ≤ I₁ ⊔ I₂)).appLE _ _
    (le_of_eq (inclusion_left_preimage I₁ I₂ V).symm)

/-- Restriction of a section of the second closed subscheme to the scheme-theoretic
intersection. -/
noncomputable def interRestrictRight (V : X.Opens) :
    Γ(I₂.subscheme, I₂.subschemeι ⁻¹ᵁ V) ⟶
      Γ((I₁ ⊔ I₂).subscheme, (I₁ ⊔ I₂).subschemeι ⁻¹ᵁ V) :=
  (inclusion (le_sup_right : I₂ ≤ I₁ ⊔ I₂)).appLE _ _
    (le_of_eq (inclusion_right_preimage I₁ I₂ V).symm)

/-- Restricting a section of `𝒪_X` to the first closed subscheme and then to the intersection is
restricting it to the intersection. -/
@[reassoc]
theorem app_interRestrictLeft (V : X.Opens) :
    I₁.subschemeι.app V ≫ interRestrictLeft I₁ I₂ V = (I₁ ⊔ I₂).subschemeι.app V := by
  rw [interRestrictLeft, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE,
    Stacks.AffineAlgebraEquivalence.appLE_congr_hom
      (inclusion_subschemeι (le_sup_left : I₁ ≤ I₁ ⊔ I₂)) _ (le_of_eq rfl),
    Scheme.Hom.appLE_eq_app]

/-- Restricting a section of `𝒪_X` to the second closed subscheme and then to the intersection is
restricting it to the intersection. -/
@[reassoc]
theorem app_interRestrictRight (V : X.Opens) :
    I₂.subschemeι.app V ≫ interRestrictRight I₁ I₂ V = (I₁ ⊔ I₂).subschemeι.app V := by
  rw [interRestrictRight, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE,
    Stacks.AffineAlgebraEquivalence.appLE_congr_hom
      (inclusion_subschemeι (le_sup_right : I₂ ≤ I₁ ⊔ I₂)) _ (le_of_eq rfl),
    Scheme.Hom.appLE_eq_app]

/-- The restriction to the intersection is natural in the open set. -/
theorem interRestrictLeft_map {U V : X.Opens} (hUV : U ≤ V) :
    interRestrictLeft I₁ I₂ V ≫ (I₁ ⊔ I₂).subscheme.presheaf.map
        (homOfLE ((I₁ ⊔ I₂).subschemeι.preimage_mono hUV)).op =
      I₁.subscheme.presheaf.map (homOfLE (I₁.subschemeι.preimage_mono hUV)).op ≫
        interRestrictLeft I₁ I₂ U := by
  rw [interRestrictLeft, interRestrictLeft, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

/-- The restriction to the intersection is natural in the open set. -/
theorem interRestrictRight_map {U V : X.Opens} (hUV : U ≤ V) :
    interRestrictRight I₁ I₂ V ≫ (I₁ ⊔ I₂).subscheme.presheaf.map
        (homOfLE ((I₁ ⊔ I₂).subschemeι.preimage_mono hUV)).op =
      I₂.subscheme.presheaf.map (homOfLE (I₂.subschemeι.preimage_mono hUV)).op ≫
        interRestrictRight I₁ I₂ U := by
  rw [interRestrictRight, interRestrictRight, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

end Restriction

section Affine

variable (I₁ I₂ : X.IdealSheafData)

/-- Over an affine open, a section of `𝒪_X` restricts to zero on the closed subscheme of `I`
exactly when it lies in `I.ideal U`. -/
private theorem app_subschemeι_eq_zero_iff (I : X.IdealSheafData) (U : X.affineOpens)
    (x : Γ(X, U.1)) : (I.subschemeι.app U.1).hom x = 0 ↔ x ∈ I.ideal U := by
  rw [← ker_subschemeι_app, RingHom.mem_ker]

/-- **Uniqueness over an affine open.** A section of `𝒪_X` over an affine open is determined by
its restrictions to the two closed subschemes, because the two restrictions have kernels
`I₁.ideal U` and `I₂.ideal U`, which meet in zero. -/
theorem app_ext_of_isAffineOpen (h : I₁ ⊓ I₂ = ⊥) (U : X.affineOpens) {c d : Γ(X, U.1)}
    (h₁ : (I₁.subschemeι.app U.1).hom c = (I₁.subschemeι.app U.1).hom d)
    (h₂ : (I₂.subschemeι.app U.1).hom c = (I₂.subschemeι.app U.1).hom d) : c = d := by
  have hm₁ : c - d ∈ I₁.ideal U :=
    (app_subschemeι_eq_zero_iff I₁ U _).mp (by rw [map_sub, h₁, sub_self])
  have hm₂ : c - d ∈ I₂.ideal U :=
    (app_subschemeι_eq_zero_iff I₂ U _).mp (by rw [map_sub, h₂, sub_self])
  have hmem : c - d ∈ (I₁ ⊓ I₂).ideal U := by rw [ideal_inf]; exact ⟨hm₁, hm₂⟩
  rw [h] at hmem
  simpa [sub_eq_zero] using hmem

/-- **Existence over an affine open.** Over an affine open the restriction to a closed subscheme
is surjective with kernel the ideal, so a compatible pair of sections is the image of a section
of `𝒪_X`: lift both, subtract the `I₁`-part of their difference. No hypothesis on the ideal
sheaves is needed for existence. -/
theorem exists_app_eq_of_isAffineOpen (U : X.affineOpens)
    (a : Γ(I₁.subscheme, I₁.subschemeι ⁻¹ᵁ U.1)) (b : Γ(I₂.subscheme, I₂.subschemeι ⁻¹ᵁ U.1))
    (hab : (interRestrictLeft I₁ I₂ U.1).hom a = (interRestrictRight I₁ I₂ U.1).hom b) :
    ∃ c : Γ(X, U.1), (I₁.subschemeι.app U.1).hom c = a ∧ (I₂.subschemeι.app U.1).hom c = b := by
  obtain ⟨p, hp⟩ := I₁.subschemeι_app_surjective U a
  obtain ⟨q, hq⟩ := I₂.subschemeι_app_surjective U b
  have hpq : p - q ∈ (I₁ ⊔ I₂).ideal U := by
    rw [← app_subschemeι_eq_zero_iff, map_sub, sub_eq_zero]
    have e₁ : ((I₁ ⊔ I₂).subschemeι.app U.1).hom p = (interRestrictLeft I₁ I₂ U.1).hom a := by
      rw [← hp, ← app_interRestrictLeft]; rfl
    have e₂ : ((I₁ ⊔ I₂).subschemeι.app U.1).hom q = (interRestrictRight I₁ I₂ U.1).hom b := by
      rw [← hq, ← app_interRestrictRight]; rfl
    rw [e₁, e₂, hab]
  rw [ideal_sup] at hpq
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hpq
  refine ⟨p - x, ?_, ?_⟩
  · rw [map_sub, hp, (app_subschemeι_eq_zero_iff I₁ U x).mpr hx, sub_zero]
  · have hpx : p - x = q + y := by linear_combination -hxy
    rw [hpx, map_add, hq, (app_subschemeι_eq_zero_iff I₂ U y).mpr hy, add_zero]

end Affine

section General

variable (I₁ I₂ : X.IdealSheafData)

/-- The affine opens contained in a given open, as an index type for the sheaf conditions
below. -/
private abbrev AffineSub (V : X.Opens) : Type u := {U : X.affineOpens // U.1 ≤ V}

private theorem le_iSup_affineSub (V : X.Opens) : V ≤ ⨆ i : AffineSub (X := X) V, i.1.1 := by
  intro x hx
  obtain ⟨W, hW, hxW, hWV⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx
  exact Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, hWV⟩, hxW⟩

private theorem preimage_le_iSup_affineSub {Y : Scheme.{u}} (f : Y ⟶ X) (V : X.Opens) :
    f ⁻¹ᵁ V ≤ ⨆ i : AffineSub (X := X) V, f ⁻¹ᵁ i.1.1 :=
  (f.preimage_iSup _) ▸ f.preimage_mono (le_iSup_affineSub V)

/-- A section of `𝒪_X` whose restrictions to the affine opens inside `V` restrict on the closed
subscheme of `I` to the restrictions of `a` restricts to `a`. -/
private theorem app_eq_of_forall_app_affineSub (I : X.IdealSheafData) (V : X.Opens)
    (cc : Γ(X, V)) (a : Γ(I.subscheme, I.subschemeι ⁻¹ᵁ V)) (c : ∀ i : AffineSub (X := X) V,
      Γ(X, i.1.1))
    (hcc : ∀ i, (X.presheaf.map (homOfLE i.2).op).hom cc = c i)
    (hc : ∀ i, (I.subschemeι.app i.1.1).hom (c i)
      = (I.subscheme.presheaf.map (homOfLE (I.subschemeι.preimage_mono i.2)).op).hom a) :
    (I.subschemeι.app V).hom cc = a := by
  refine I.subscheme.sheaf.eq_of_locally_eq'
    (fun i : AffineSub (X := X) V => I.subschemeι ⁻¹ᵁ i.1.1) (I.subschemeι ⁻¹ᵁ V)
    (fun i => homOfLE (I.subschemeι.preimage_mono i.2))
    (preimage_le_iSup_affineSub I.subschemeι V) _ _ fun i => ?_
  exact (app_map I.subschemeι (homOfLE i.2) cc).symm.trans
    ((congrArg (I.subschemeι.app i.1.1).hom (hcc i)).trans (hc i))

/-- **Uniqueness over an arbitrary open.** A section of `𝒪_X` over any open is determined by its
restrictions to the two closed subschemes: the affine opens form a basis, the statement holds
over each of them, and the structure sheaf is separated. -/
theorem app_ext_of_inf_eq_bot (h : I₁ ⊓ I₂ = ⊥) (V : X.Opens) {c d : Γ(X, V)}
    (h₁ : (I₁.subschemeι.app V).hom c = (I₁.subschemeι.app V).hom d)
    (h₂ : (I₂.subschemeι.app V).hom c = (I₂.subschemeι.app V).hom d) : c = d := by
  have key : ∀ i : AffineSub (X := X) V, (X.presheaf.map (homOfLE i.2).op).hom c
      = (X.presheaf.map (homOfLE i.2).op).hom d := fun i =>
    app_ext_of_isAffineOpen I₁ I₂ h i.1
      (by rw [app_map, app_map, h₁]) (by rw [app_map, app_map, h₂])
  exact X.sheaf.eq_of_locally_eq' (fun i : AffineSub (X := X) V => i.1.1) V
    (fun i => homOfLE i.2) (le_iSup_affineSub V) c d key

/-- **Existence over an arbitrary open.** A pair of sections of the two closed subschemes which
agree on the scheme-theoretic intersection is the restriction of a section of `𝒪_X`. The affine
case is glued over the basis of affine opens; the compatibility of the local solutions is
`Stacks.AffineClosedUnion.app_ext_of_inf_eq_bot`, which is where `I₁ ⊓ I₂ = ⊥` is used. -/
theorem exists_app_eq_of_inf_eq_bot (h : I₁ ⊓ I₂ = ⊥) (V : X.Opens)
    (a : Γ(I₁.subscheme, I₁.subschemeι ⁻¹ᵁ V)) (b : Γ(I₂.subscheme, I₂.subschemeι ⁻¹ᵁ V))
    (hab : (interRestrictLeft I₁ I₂ V).hom a = (interRestrictRight I₁ I₂ V).hom b) :
    ∃ c : Γ(X, V), (I₁.subschemeι.app V).hom c = a ∧ (I₂.subschemeι.app V).hom c = b := by
  classical
  have hcompat : ∀ i : AffineSub (X := X) V,
      (interRestrictLeft I₁ I₂ i.1.1).hom
          ((I₁.subscheme.presheaf.map (homOfLE (I₁.subschemeι.preimage_mono i.2)).op).hom a)
        = (interRestrictRight I₁ I₂ i.1.1).hom
          ((I₂.subscheme.presheaf.map (homOfLE (I₂.subschemeι.preimage_mono i.2)).op).hom b) :=
    fun i => by
      have e₁ := ConcreteCategory.congr_hom (interRestrictLeft_map I₁ I₂ i.2) a
      have e₂ := ConcreteCategory.congr_hom (interRestrictRight_map I₁ I₂ i.2) b
      simp only [ConcreteCategory.comp_apply] at e₁ e₂
      rw [← e₁, ← e₂, hab]
  choose c hc₁ hc₂ using fun i : AffineSub (X := X) V =>
    exists_app_eq_of_isAffineOpen I₁ I₂ i.1 _ _ (hcompat i)
  have hcc : TopCat.Presheaf.IsCompatible X.presheaf
      (fun i : AffineSub (X := X) V => i.1.1) c := by
    intro i j
    refine app_ext_of_inf_eq_bot I₁ I₂ h _ ?_ ?_
    · rw [app_map, app_map, hc₁ i, hc₁ j]; exact map_map_eq _ _ _ _ a
    · rw [app_map, app_map, hc₂ i, hc₂ j]; exact map_map_eq _ _ _ _ b
  obtain ⟨cc, hcc1, -⟩ := X.sheaf.existsUnique_gluing'
    (fun i : AffineSub (X := X) V => i.1.1) V (fun i => homOfLE i.2) (le_iSup_affineSub V) c hcc
  refine ⟨cc, ?_, ?_⟩
  · exact app_eq_of_forall_app_affineSub I₁ V cc a c hcc1 hc₁
  · exact app_eq_of_forall_app_affineSub I₂ V cc b c hcc1 hc₂

/-- **The cartesian square of sections, in element form.** -/
theorem existsUnique_app_eq_of_inf_eq_bot (h : I₁ ⊓ I₂ = ⊥) (V : X.Opens)
    (a : Γ(I₁.subscheme, I₁.subschemeι ⁻¹ᵁ V)) (b : Γ(I₂.subscheme, I₂.subschemeι ⁻¹ᵁ V))
    (hab : (interRestrictLeft I₁ I₂ V).hom a = (interRestrictRight I₁ I₂ V).hom b) :
    ∃! c : Γ(X, V), (I₁.subschemeι.app V).hom c = a ∧ (I₂.subschemeι.app V).hom c = b := by
  obtain ⟨c, hc₁, hc₂⟩ := exists_app_eq_of_inf_eq_bot I₁ I₂ h V a b hab
  exact ⟨c, ⟨hc₁, hc₂⟩, fun d hd =>
    app_ext_of_inf_eq_bot I₁ I₂ h V (hd.1.trans hc₁.symm) (hd.2.trans hc₂.symm)⟩

/-- **The form [Stacks, Tag 09NX] consumes.** A section of the structure sheaf of the second
closed subscheme which vanishes on the scheme-theoretic intersection is the restriction of a
unique section of `𝒪_X` vanishing on the first closed subscheme. -/
theorem exists_app_eq_zero_of_inf_eq_bot (h : I₁ ⊓ I₂ = ⊥) (V : X.Opens)
    (b : Γ(I₂.subscheme, I₂.subschemeι ⁻¹ᵁ V))
    (hb : (interRestrictRight I₁ I₂ V).hom b = 0) :
    ∃! c : Γ(X, V), (I₁.subschemeι.app V).hom c = 0 ∧ (I₂.subschemeι.app V).hom c = b :=
  existsUnique_app_eq_of_inf_eq_bot I₁ I₂ h V 0 b (by rw [map_zero, hb])

/-! ### The hypothesis `I₁ ⊓ I₂ = ⊥` is load-bearing

The two controls below show that the uniqueness statement is *false* without the hypothesis, by
deriving an absurdity from the hypothesis-free form. They are machine-checked, not commentary.
Existence, by contrast, uses the hypothesis only through uniqueness — the affine case
`Stacks.AffineClosedUnion.exists_app_eq_of_isAffineOpen` carries no hypothesis on the ideal
sheaves at all, and `I₁ ⊓ I₂ = ⊥` enters the globalisation only to see that the local solutions
agree on overlaps. No claim is made here that existence fails without it.
-/

/-- **Negative control.** Dropping `I₁ ⊓ I₂ = ⊥` from
`Stacks.AffineClosedUnion.app_ext_of_inf_eq_bot` makes the sections of every scheme over every
open a subsingleton: instantiate at `I₁ = I₂ = ⊤`, whose closed subscheme is empty, so both
hypotheses hold vacuously. -/
theorem control_subsingleton_of_app_ext_without_inf_eq_bot
    (H : ∀ (Y : Scheme.{u}) (J₁ J₂ : Y.IdealSheafData) (V : Y.Opens) (c d : Γ(Y, V)),
      (J₁.subschemeι.app V).hom c = (J₁.subschemeι.app V).hom d →
      (J₂.subschemeι.app V).hom c = (J₂.subschemeι.app V).hom d → c = d)
    (Y : Scheme.{u}) (V : Y.Opens) : Subsingleton Γ(Y, V) :=
  ⟨fun c d => H Y ⊤ ⊤ V c d (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩

/-- **Negative control, in refuting form.** The hypothesis-free uniqueness statement is
inconsistent: it forces `Γ(Spec ℤ, ⊤)` to be a subsingleton. -/
theorem control_app_ext_without_inf_eq_bot_false
    (H : ∀ (Y : Scheme.{u}) (J₁ J₂ : Y.IdealSheafData) (V : Y.Opens) (c d : Γ(Y, V)),
      (J₁.subschemeι.app V).hom c = (J₁.subschemeι.app V).hom d →
      (J₂.subschemeι.app V).hom c = (J₂.subschemeι.app V).hom d → c = d) : False :=
  have : Subsingleton (ULift.{u} ℤ) :=
    have := control_subsingleton_of_app_ext_without_inf_eq_bot H (Spec (.of (ULift.{u} ℤ))) ⊤
    (Scheme.ΓSpecIso (.of (ULift.{u} ℤ))).commRingCatIsoToRingEquiv.symm.injective.subsingleton
  not_subsingleton (ULift.{u} ℤ) this

end General


end Stacks.AffineClosedUnion

end
