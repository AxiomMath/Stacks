module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerConstraints
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleInternalHom
public import StacksFrontier.AlgebraicGeometry.Divisors.SectionContraction

/-!
# Contraction with a section, read off the evaluation pairing

Let `𝒪` be a sheaf of commutative rings on a site `(C, J)` and let `L` be an invertible
`𝒪`-module with a global section `s`.  This file reads the contraction
`Stacks.SheafOfModules.Invertible.sectionContraction` with `s` on the sections: it evaluates the
pairing `L^{⊗ -1} ⊗ L ≅ 𝒪` at `x ⊗ s`.  Together with the identification of two modules carrying
pairings against one invertible module it is what turns the existence of an isomorphism
`𝒪_X(D) ≅ L` into the existence of one matching prescribed sections.

## Main results

* `Stacks.SheafOfModules.Invertible.sectionContraction_app`: contraction with `s` evaluates the
  pairing at `x ⊗ s`.
* `Stacks.SheafOfModules.Invertible.exists_iso_of_tensorPairing`: two modules carrying pairings
  against the same invertible module, with the same value module, are isomorphic by an
  isomorphism matching the two pairings.
* `Stacks.SheafOfModules.Invertible.eq_of_tensorPairing_eq`: a section is determined by the
  values of the pairing on it, because currying against the pairing is bijective.

## Implementation notes

The three coherence constraints of the sheaf tensor product entering the contraction — the left
unitor, the braiding, and the functoriality in one factor — are all of the shape "sheafify a
morphism of presheaves of modules, then apply the counit of sheafification".  So each of them is
computed on the image of a pure tensor under the unit of sheafification by
`Stacks.SheafOfModules.sheafify_map_toSheafify_app`, which is the naturality of that unit, and
`Stacks.SheafOfModules.counit_toSheafify_app`, which is a triangle identity.  No description of
the sections of a sheafified tensor product is needed: the unit of sheafification carries enough
pure tensors to pin the composite down, because the contraction is read at the *one* section
`1 ⊗ x` of `𝒪 ⊗ L^{⊗ -1}`.

The identification of two modules with pairings against one invertible `G` does not go through
the sections either.  Precomposition with a pairing `M ⊗ G ⟶ H` is a bijection from the
morphisms into `M` onto the morphisms out of `- ⊗ G`
(`Stacks.SheafOfModules.Invertible.tensorHom_bijective`), so each of the two pairings is the
image of a unique morphism between the two modules; the two morphisms compose to the identity on
each side because the identity is the unique morphism whose image is the pairing itself.

## References

* [Stacks Project, Tag 0841](https://stacks.math.columbia.edu/tag/0841)
* [Stacks Project, Tag 0843](https://stacks.math.columbia.edu/tag/0843)
* [Stacks Project, Tag 0847](https://stacks.math.columbia.edu/tag/0847)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Opposite
open scoped TensorProduct
open Stacks.PresheafOfModules.TensorInternalHom
open Stacks.SheafOfModules.TensorSheafification
  (structureRingPresheaf structureSheaf sheafify sheafifyAdjunction toSheafify)

universe u w

namespace Stacks.SheafOfModules.Invertible

open AlgebraicGeometry.SheafOfModules (IsInvertible)

variable {C : Type u} [Category.{w} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

-- The monoidal structure on presheaves of modules over the structure sheaf, in the spelling
-- forced by the sheafification functor: instance search does not find it through the projection
-- `(structureSheaf O hO).obj`, so it is the local instance of
-- `StacksFrontier.AlgebraicGeometry.Divisors.InvertibleInternalHom`, re-enabled here.
attribute [local instance] monoidalCategoryStructureSheaf

/-- That monoidal structure is symmetric, because `O` is commutative. -/
local instance symmetricCategoryStructureSheaf :
    SymmetricCategory (_root_.PresheafOfModules.{w} (structureSheaf O hO).obj) :=
  _root_.PresheafOfModulesOfCommRing.symmetricCategory (R := O)

/-! ### The coherence constraints of the sheaf tensor product on pure tensors -/

/-- **The left unit constraint of the sheaf tensor product on a pure tensor.**  It is the
presheaf-level unitor followed by the counit of sheafification. -/
theorem tensorProductLeftUnitor_hom_toSheafify_tmul
    (M : _root_.SheafOfModules.{w} (structureSheaf O hO)) (W : Cᵒᵖ)
    (r : (structureSheaf O hO).obj.obj W) (x : M.val.obj W) :
    ((tensorProductLeftUnitor O hO M).hom.val.app W).hom
        ((toSheafify O hO (valPresheaf O hO
            (_root_.SheafOfModules.unit (structureSheaf O hO)) ⊗ valPresheaf O hO M)).app W
          (r ⊗ₜ x)) = r • x :=
  (congrArg (fun z ↦ ((sheafifyAdjunction O hO).counit.app M).val.app W z)
      (Stacks.SheafOfModules.sheafify_map_toSheafify_app O hO (λ_ M.val).hom W (r ⊗ₜ x))).trans
    ((Stacks.SheafOfModules.counit_toSheafify_app O hO M W ((λ_ M.val).hom.app W (r ⊗ₜ x))).trans
      (ModuleCat.MonoidalCategory.leftUnitor_hom_apply r x))

/-- **The braiding of the sheaf tensor product on a pure tensor**, read off the pairing it
precedes: the pairing attached to a braided isomorphism evaluates the original pairing on the
swapped tensor. -/
theorem tensorPairing_braiding_tmul
    (G M H : _root_.SheafOfModules.{w} (structureSheaf O hO))
    (ev : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        (M)).obj (G)) ≅ H)
    (W : Cᵒᵖ) (y : G.val.obj W) (x : M.val.obj W) :
    tensorHomAt O (valPresheaf O hO G) (valPresheaf O hO M) (valPresheaf O hO H)
        (tensorPairing O hO M G H (tensorProductBraiding O hO G M ≪≫ ev)) W (y ⊗ₜ x) =
      tensorHomAt O (valPresheaf O hO M) (valPresheaf O hO G) (valPresheaf O hO H)
        (tensorPairing O hO G M H ev) W (x ⊗ₜ y) :=
  congrArg (fun z ↦ (ev.hom.val.app W).hom z)
    (Stacks.SheafOfModules.sheafify_map_toSheafify_app O hO (β_ G.val M.val).hom W (y ⊗ₜ x))

/-- **Moving an isomorphism of the second tensor factor across the pairing.**  The pairing
attached to `M ⊗ G ≅ M ⊗ G' ≅ H` evaluates the pairing of `M ⊗ G' ≅ H` on the image of the
second factor. -/
theorem tensorPairing_tensorProductIso_tmul
    (G G' M H : _root_.SheafOfModules.{w} (structureSheaf O hO)) (e : G ≅ G')
    (ev : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        (M)).obj (G')) ≅ H)
    (W : Cᵒᵖ) (x : M.val.obj W) (t : G.val.obj W) :
    tensorHomAt O (valPresheaf O hO M) (valPresheaf O hO G) (valPresheaf O hO H)
        (tensorPairing O hO G M H (tensorProductIso O hO (Iso.refl M) e ≪≫ ev)) W (x ⊗ₜ t) =
      tensorHomAt O (valPresheaf O hO M) (valPresheaf O hO G') (valPresheaf O hO H)
        (tensorPairing O hO G' M H ev) W (x ⊗ₜ (e.hom.val.app W).hom t) :=
  congrArg (fun z ↦ (ev.hom.val.app W).hom z)
    (Stacks.SheafOfModules.sheafify_map_toSheafify_app O hO
      ((Iso.refl M).hom.val ⊗ₘ e.hom.val) W (x ⊗ₜ t))

/-! ### Contraction with a section -/

variable (L : _root_.SheafOfModules.{w} (structureSheaf O hO)) [IsInvertible O hO L]

/-- **Contraction with a global section, read on the sections**: it evaluates the pairing
`L^{⊗ -1} ⊗ L ≅ 𝒪` at `x ⊗ s`.

Composing with the unit constraint `𝒪 ⊗ L^{⊗ -1} ≅ L^{⊗ -1}` turns the contraction into
multiplication by `s` in the first factor followed by the braiding and the pairing, and the
section `x` is the value of the unit constraint on `1 ⊗ x`. -/
theorem sectionContraction_app (s : L.sections) (W : Cᵒᵖ)
    (x : (inverseSheaf O hO L).val.obj W) :
    ((sectionContraction O hO L s).val.app W).hom x =
      tensorHomAt O (valPresheaf O hO (inverseSheaf O hO L)) (valPresheaf O hO L)
        (valPresheaf O hO (_root_.SheafOfModules.unit (structureSheaf O hO)))
        (tensorPairing O hO L (inverseSheaf O hO L)
          (_root_.SheafOfModules.unit (structureSheaf O hO)) (inverseSheafEvaluation O hO L)) W
        (x ⊗ₜ s.eval W) := by
  have hunit : ((inverseSheafUnitIso O hO L).hom.val.app W).hom
      ((toSheafify O hO (valPresheaf O hO (_root_.SheafOfModules.unit (structureSheaf O hO)) ⊗
          valPresheaf O hO (inverseSheaf O hO L))).app W
        ((1 : (structureSheaf O hO).obj.obj W) ⊗ₜ x)) = x :=
    (tensorProductLeftUnitor_hom_toSheafify_tmul O hO (inverseSheaf O hO L) W 1 x).trans
      (one_smul _ x)
  have hfac : (inverseSheafUnitIso O hO L).hom ≫ sectionContraction O hO L s =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, w, w, w, w}
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
            (inverseSheaf O hO L)).map (L.unitHomEquiv.symm s) ≫
        (tensorProductBraiding O hO L (inverseSheaf O hO L) ≪≫
          inverseSheafEvaluation O hO L).hom := by
    unfold sectionContraction
    exact Eq.trans (Iso.hom_inv_id_assoc (inverseSheafUnitIso O hO L) _) rfl
  have hmul : ((L.unitHomEquiv.symm s).val.app W).hom (1 : (structureSheaf O hO).obj.obj W) =
      s.eval W := by
    show (1 : (structureSheaf O hO).obj.obj W) • s.eval W = s.eval W
    exact one_smul _ _
  refine Eq.trans
    (congrArg (fun z ↦ ((sectionContraction O hO L s).val.app W).hom z) hunit.symm) ?_
  show (((inverseSheafUnitIso O hO L).hom ≫ sectionContraction O hO L s).val.app W).hom
      ((toSheafify O hO (valPresheaf O hO (_root_.SheafOfModules.unit (structureSheaf O hO)) ⊗
        valPresheaf O hO (inverseSheaf O hO L))).app W
          ((1 : (structureSheaf O hO).obj.obj W) ⊗ₜ x)) = _
  rw [hfac]
  refine Eq.trans ?_ (tensorPairing_braiding_tmul O hO L (inverseSheaf O hO L)
    (_root_.SheafOfModules.unit (structureSheaf O hO)) (inverseSheafEvaluation O hO L) W
    (s.eval W) x)
  refine Eq.trans ?_ (congrArg (fun z ↦ tensorHomAt O (valPresheaf O hO L)
    (valPresheaf O hO (inverseSheaf O hO L))
    (valPresheaf O hO (_root_.SheafOfModules.unit (structureSheaf O hO)))
    (tensorPairing O hO (inverseSheaf O hO L) L
      (_root_.SheafOfModules.unit (structureSheaf O hO))
      (tensorProductBraiding O hO L (inverseSheaf O hO L) ≪≫
        inverseSheafEvaluation O hO L)) W (z ⊗ₜ x)) hmul)
  exact congrArg (fun z ↦ ((tensorProductBraiding O hO L (inverseSheaf O hO L) ≪≫
      inverseSheafEvaluation O hO L).hom.val.app W).hom z)
    (Stacks.SheafOfModules.sheafify_map_toSheafify_app O hO
      ((L.unitHomEquiv.symm s).val ▷ valPresheaf O hO (inverseSheaf O hO L)) W
      ((1 : (structureSheaf O hO).obj.obj W) ⊗ₜ x))

/-- **The identification of `L^{⊗ -1}` with the sheaf of ideals it cuts out carries the inclusion
of that sheaf of ideals to the contraction**: it is the factorisation of the contraction through
its image. -/
theorem inverseSheafIsoSectionIdeal_hom_ι (s : L.sections)
    (hs : Mono (L.unitHomEquiv.symm s)) :
    (inverseSheafIsoSectionIdeal O hO L s hs).hom ≫ (sectionIdealSubmodule O hO L s).ι =
      sectionContraction O hO L s :=
  Stacks.SheafOfModules.ImageSubsheaf.toImage_ι (sectionContraction O hO L s)

/-! ### A section is determined by the pairing, and two pairings identify their modules -/

/-- Congruence of the value of a morphism out of a tensor product in the left entry of a pure
tensor. -/
private theorem tensorHomAt_tmul_congr
    {F G H : _root_.PresheafOfModules.{w} (Oforget O)} (b : F ⊗ G ⟶ H) (W : Cᵒᵖ)
    {x x' : F.obj W} (h : x = x') (y : G.obj W) :
    tensorHomAt O F G H b W (x ⊗ₜ y) = tensorHomAt O F G H b W (x' ⊗ₜ y) := by
  rw [h]

/-- **A section is determined by the values of the pairing on it.**  Currying against the pairing
`M ⊗ G ⟶ H` is injective on the sections over an object, for `G` invertible. -/
theorem eq_of_tensorPairing_eq (G M H : _root_.SheafOfModules.{w} (structureSheaf O hO))
    [IsInvertible O hO G]
    (ev : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        (M)).obj (G)) ≅ H) (U : C)
    (a b : (valPresheaf O hO M).obj (op U))
    (h : ∀ (V : Cᵒᵖ) (q : V.unop ⟶ U) (t : G.val.obj V),
      tensorHomAt O (valPresheaf O hO M) (valPresheaf O hO G) (valPresheaf O hO H)
          (tensorPairing O hO G M H ev) V ((valPresheaf O hO M).restrictₛₗ q.op a ⊗ₜ t) =
        tensorHomAt O (valPresheaf O hO M) (valPresheaf O hO G) (valPresheaf O hO H)
          (tensorPairing O hO G M H ev) V ((valPresheaf O hO M).restrictₛₗ q.op b ⊗ₜ t)) :
    a = b := by
  refine (tensorCurryLinearEquiv O hO G M H ev U).injective ?_
  refine homSection_ext O (valPresheaf O hO G) (valPresheaf O hO H) U _ _ fun V q t ↦ ?_
  rw [tensorCurryLinearEquiv_apply, tensorCurryLinearEquiv_apply]
  exact h V q t

/-- **A global section is determined by the values of the pairing on it.**  The values on a
global section at the objects of the site already determine the values on its restrictions, so
`Stacks.SheafOfModules.Invertible.eq_of_tensorPairing_eq` applies at every object. -/
theorem sections_eq_of_tensorPairing_eq
    (G M H : _root_.SheafOfModules.{w} (structureSheaf O hO)) [IsInvertible O hO G]
    (ev : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        (M)).obj (G)) ≅ H) (a b : M.sections)
    (h : ∀ (V : Cᵒᵖ) (t : (valPresheaf O hO G).obj V),
      tensorHomAt O (valPresheaf O hO M) (valPresheaf O hO G) (valPresheaf O hO H)
          (tensorPairing O hO G M H ev) V (a.eval V ⊗ₜ t) =
        tensorHomAt O (valPresheaf O hO M) (valPresheaf O hO G) (valPresheaf O hO H)
          (tensorPairing O hO G M H ev) V (b.eval V ⊗ₜ t)) :
    a = b := by
  refine _root_.PresheafOfModules.sections_ext a b fun W ↦ ?_
  obtain ⟨U⟩ := W
  refine eq_of_tensorPairing_eq O hO G M H ev U _ _ fun V q t ↦ ?_
  refine (tensorHomAt_tmul_congr O (tensorPairing O hO G M H ev) V
    (_root_.PresheafOfModules.sections_property a q.op) t).trans ?_
  exact (h V t).trans (tensorHomAt_tmul_congr O (tensorPairing O hO G M H ev) V
    (_root_.PresheafOfModules.sections_property b q.op).symm t)

/-- **Morphisms between two modules compatible with the pairings against `G` are mutually
inverse.**  The identity is the unique morphism whose image under precomposition is the pairing. -/
private theorem comp_eq_id_of_tensorPairing
    (G M N H : _root_.SheafOfModules.{w} (structureSheaf O hO)) [IsInvertible O hO G]
    (evM : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        (M)).obj (G)) ≅ H)
    (evN : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        (N)).obj (G)) ≅ H)
    (f : valPresheaf O hO M ⟶ valPresheaf O hO N) (g : valPresheaf O hO N ⟶ valPresheaf O hO M)
    (hf : (f ▷ valPresheaf O hO G) ≫ tensorPairing O hO G N H evN = tensorPairing O hO G M H evM)
    (hg : (g ▷ valPresheaf O hO G) ≫ tensorPairing O hO G M H evM =
      tensorPairing O hO G N H evN) :
    f ≫ g = 𝟙 (valPresheaf O hO M) := by
  refine (tensorHom_bijective O hO G M H evM (valPresheaf O hO M)).1 ?_
  show ((f ≫ g) ▷ valPresheaf O hO G) ≫ tensorPairing O hO G M H evM =
    (𝟙 (valPresheaf O hO M) ▷ valPresheaf O hO G) ≫ tensorPairing O hO G M H evM
  rw [comp_whiskerRight, id_whiskerRight, Category.assoc, hg, hf, Category.id_comp]

/-- **Two modules with pairings against one invertible module are isomorphic, compatibly with
the pairings.**  Precomposition with a pairing is a bijection from the morphisms into the module
onto the morphisms out of the tensor product, so each pairing is the image of a unique morphism
between the two modules, and the two morphisms are mutually inverse because the identity is the
unique morphism whose image is the pairing itself. -/
theorem exists_iso_of_tensorPairing (G M N H : _root_.SheafOfModules.{w} (structureSheaf O hO))
    [IsInvertible O hO G]
    (evM : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        (M)).obj (G)) ≅ H)
    (evN : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        (N)).obj (G)) ≅ H) :
    ∃ φ : M ≅ N, ∀ (W : Cᵒᵖ) (x : M.val.obj W) (t : G.val.obj W),
      tensorHomAt O (valPresheaf O hO N) (valPresheaf O hO G) (valPresheaf O hO H)
          (tensorPairing O hO G N H evN) W ((φ.hom.val.app W).hom x ⊗ₜ t) =
        tensorHomAt O (valPresheaf O hO M) (valPresheaf O hO G) (valPresheaf O hO H)
          (tensorPairing O hO G M H evM) W (x ⊗ₜ t) := by
  obtain ⟨f, hf0⟩ := (tensorHom_bijective O hO G N H evN (valPresheaf O hO M)).2
    (tensorPairing O hO G M H evM)
  obtain ⟨g, hg0⟩ := (tensorHom_bijective O hO G M H evM (valPresheaf O hO N)).2
    (tensorPairing O hO G N H evN)
  have hf : (f ▷ valPresheaf O hO G) ≫ tensorPairing O hO G N H evN =
      tensorPairing O hO G M H evM := hf0
  have hg : (g ▷ valPresheaf O hO G) ≫ tensorPairing O hO G M H evM =
      tensorPairing O hO G N H evN := hg0
  have hfg := comp_eq_id_of_tensorPairing O hO G M N H evM evN f g hf hg
  have hgf := comp_eq_id_of_tensorPairing O hO G N M H evN evM g f hg hf
  refine ⟨⟨⟨f⟩, ⟨g⟩, _root_.SheafOfModules.hom_ext hfg, _root_.SheafOfModules.hom_ext hgf⟩,
    fun W x t ↦ ?_⟩
  exact congrArg (fun φ ↦ tensorHomAt O (valPresheaf O hO M) (valPresheaf O hO G)
    (valPresheaf O hO H) φ W (x ⊗ₜ t)) hf

/-! ### An isomorphism matching prescribed sections -/

/-- **An isomorphism onto an invertible module matching prescribed global sections.**  Let `L` be
an invertible module with a global section `s`, let `G` be an invertible module with a morphism
`incl : G ⟶ 𝒪` and an identification `G ≅ L^{⊗ -1}` carrying `incl` to contraction with `s`, and
let `M` carry a pairing `M ⊗ G ≅ 𝒪` together with a global section `σ` which that pairing curries
to `incl`.  Then `M ≅ L` by an isomorphism carrying `σ` to `s`.

Contracting the second factor of `L ⊗ G` into `L^{⊗ -1}` and evaluating gives a pairing
`L ⊗ G ≅ 𝒪` which curries `s` to `incl` as well, by
`Stacks.SheafOfModules.Invertible.sectionContraction_app`; so `M` and `L` carry pairings against
the same invertible module, hence are isomorphic compatibly with the two pairings, and the
isomorphism carries `σ` to `s` because both curry to `incl` and currying is injective. -/
theorem exists_iso_of_sectionContraction_eq
    (L G M : _root_.SheafOfModules.{w} (structureSheaf O hO))
    [IsInvertible O hO L] [IsInvertible O hO G]
    (incl : G ⟶ _root_.SheafOfModules.unit (structureSheaf O hO)) (s : L.sections)
    (h₀ : G ≅ inverseSheaf O hO L)
    (hincl : h₀.hom ≫ sectionContraction O hO L s = incl)
    (ev : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        (M)).obj (G)) ≅ _root_.SheafOfModules.unit (structureSheaf O hO))
    (σ : M.sections)
    (hσ : ∀ (W : Cᵒᵖ) (t : (valPresheaf O hO G).obj W),
      tensorHomAt O (valPresheaf O hO M) (valPresheaf O hO G)
          (valPresheaf O hO (_root_.SheafOfModules.unit (structureSheaf O hO)))
          (tensorPairing O hO G M (_root_.SheafOfModules.unit (structureSheaf O hO)) ev) W
          (σ.eval W ⊗ₜ t) =
        ((valPresheafMap O hO incl).app W).hom t) :
    ∃ φ : M ≅ L, _root_.SheafOfModules.sectionsMap φ.hom σ = s := by
  have hpair : ∀ (W : Cᵒᵖ) (t : (valPresheaf O hO G).obj W),
      tensorHomAt O (valPresheaf O hO L) (valPresheaf O hO G)
          (valPresheaf O hO (_root_.SheafOfModules.unit (structureSheaf O hO)))
          (tensorPairing O hO G L (_root_.SheafOfModules.unit (structureSheaf O hO))
            (tensorProductIso O hO (Iso.refl L) h₀ ≪≫
              (tensorProductBraiding O hO L (inverseSheaf O hO L) ≪≫
                inverseSheafEvaluation O hO L))) W (s.eval W ⊗ₜ t) =
        ((valPresheafMap O hO incl).app W).hom t := by
    intro W t
    refine (tensorPairing_tensorProductIso_tmul O hO G (inverseSheaf O hO L) L
      (_root_.SheafOfModules.unit (structureSheaf O hO)) h₀
      (tensorProductBraiding O hO L (inverseSheaf O hO L) ≪≫ inverseSheafEvaluation O hO L) W
      (s.eval W) t).trans ?_
    refine (tensorPairing_braiding_tmul O hO L (inverseSheaf O hO L)
      (_root_.SheafOfModules.unit (structureSheaf O hO)) (inverseSheafEvaluation O hO L) W
      (s.eval W) ((h₀.hom.val.app W).hom t)).trans ?_
    refine (sectionContraction_app O hO L s W ((h₀.hom.val.app W).hom t)).symm.trans ?_
    exact congrArg (fun φ : G ⟶ _root_.SheafOfModules.unit (structureSheaf O hO) ↦
      (φ.val.app W).hom t) hincl
  obtain ⟨φ, hφ⟩ := exists_iso_of_tensorPairing O hO G M L
    (_root_.SheafOfModules.unit (structureSheaf O hO)) ev
    (tensorProductIso O hO (Iso.refl L) h₀ ≪≫
      (tensorProductBraiding O hO L (inverseSheaf O hO L) ≪≫ inverseSheafEvaluation O hO L))
  refine ⟨φ, ?_⟩
  refine sections_eq_of_tensorPairing_eq O hO G L
    (_root_.SheafOfModules.unit (structureSheaf O hO))
    (tensorProductIso O hO (Iso.refl L) h₀ ≪≫
      (tensorProductBraiding O hO L (inverseSheaf O hO L) ≪≫ inverseSheafEvaluation O hO L))
    _ s fun V t ↦ ?_
  exact (hφ V (σ.eval V) t).trans ((hσ V t).trans (hpair V t).symm)

end Stacks.SheafOfModules.Invertible

end
