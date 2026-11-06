module

public import StacksFrontier.Algebra.Homology.RightDerivedSecondEdgeEpi
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedBlowUpRationalSingularity
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageFibreDimension.GeneralDimension
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Morphisms.AffineFromVanishing
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BaseRingLinear
public import StacksFrontier.Homology.DerivedLinear
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.ModificationGlobalSections
public import StacksFrontier.AlgebraicGeometry.BirationalDenseOpenIso.Basic
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChangeBirational.Basic
import all StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedBlowUpRationalSingularity

/-!
# The vanishing of `R¹g_*𝒪` from the vanishing of `H¹` upstairs

Let `(A, 𝔪)` be a two-dimensional Noetherian normal local domain and let
`X' --g--> X --f--> Spec A` be two modifications with `X` normal. The low-degree Leray sequence of
`g` and `𝒪_{X'}` reads
`0 ⟶ H¹(X, g_*𝒪_{X'}) ⟶ H¹(X', 𝒪_{X'}) ⟶ H⁰(X, R¹g_*𝒪_{X'}) ⟶ H²(X, g_*𝒪_{X'})`, and its last term
vanishes because `g_*𝒪_{X'} = 𝒪_X` and the fibres of `f` have dimension at most one
([Stacks, Tag 02V7]). So the second map is onto, which is the right-hand exactness of the first
conclusion of [Stacks, Tag 0AXF].

## Main results

* `Stacks.Cohomology.LerayLowDegree.abelianSecondEdgeMap_one_surjective`: for a continuous map
  `f : X ⟶ Y` and an abelian sheaf `F` on `X` with `H²(Y, f_*F) = 0`, the second Leray edge map
  `H¹(X, F) ⟶ Γ(Y, R¹f_*F)` is surjective.
* `AlgebraicGeometry.isZero_rightDerived_evaluation_two_of_isModification`: `H²(X, 𝒪_X) = 0` for
  a normal modification `X` of the spectrum of a two-dimensional Noetherian normal local domain.
* `AlgebraicGeometry.subsingleton_sections_rightDerived_one_of_isZero`: if `H¹(X', 𝒪_{X'}) = 0`,
  then `R¹g_*𝒪_{X'}` has no nonzero global sections.
* `AlgebraicGeometry.isZero_rightDerived_one_pushforward_of_isZero`: if `H¹(X', 𝒪_{X'}) = 0`,
  then `R¹g_*𝒪_{X'} = 0`, by the third conclusion of [Stacks, Tag 0AXF].

## Implementation notes

The surjectivity of the second edge map is
`Stacks.Cohomology.RightDerivedCoEdge.epi_secondEdge_app_one_of_isZero` for `P = f_*` and
`Q = Γ(Y, -)` on abelian sheaves. The geometric inputs are in the module-valued spelling, and the
passage between the two spellings is [Stacks, Tag 01F1]: part (1)
(`Stacks.Cohomology.ModuleComparison.rightDerivedSectionsForgetIso`) for cohomology and part (2)
(`Stacks.Cohomology.ModulePushforwardComparison.rightDerived_modulePushforward_forget_iso`) for
higher direct images. The comparison `𝒪_X ⟶ g_*𝒪_{X'}` of abelian sheaves is `g.c` with the
multiplication forgotten; it is an isomorphism by [Stacks, Tag 0AY8].

## References

* [Stacks Project, Tag 0AXF](https://stacks.math.columbia.edu/tag/0AXF)
* [Stacks Project, Tag 01F2](https://stacks.math.columbia.edu/tag/01F2)
* [Stacks Project, Tag 02V7](https://stacks.math.columbia.edu/tag/02V7)
* [Stacks Project, Tag 0AY8](https://stacks.math.columbia.edu/tag/0AY8)
* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Cohomology.LerayLowDegree

attribute [local instance] abelianSheafHasSheafify

/-- **The second Leray edge map is onto when `H²(Y, f_*F) = 0`.** For a continuous map
`f : X ⟶ Y` and an abelian sheaf `F` on `X`, the map `H¹(X, F) ⟶ Γ(Y, R¹f_*F)` is surjective as
soon as `H²(Y, f_*F)` vanishes: this is the exactness of the five-term sequence at
`Γ(Y, R¹f_*F)`. -/
theorem abelianSecondEdgeMap_one_surjective {X Y : TopCat.{u}} (f : X ⟶ Y)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (h : IsZero ((abelianCohomology.{u, u} Y ⊤ 2).obj ((abelianPushforward.{u, u} f).obj F))) :
    Function.Surjective ((abelianSecondEdgeMap.{u, u} f 1).app F) :=
  (AddCommGrpCat.epi_iff_surjective _).1
    (RightDerivedCoEdge.epi_secondEdge_app_one_of_isZero (abelianPushforward.{u, u} f)
      (abelianSections.{u, u} Y ⊤) F h)

/-- **`Γ(Y, R¹f_*F) = 0` when `H¹(X, F) = 0` and `H²(Y, f_*F) = 0`.** The second Leray edge map
is onto by `abelianSecondEdgeMap_one_surjective`, and its source vanishes. -/
theorem isZero_abelianSections_rightDerived_one_of_isZero {X Y : TopCat.{u}} (f : X ⟶ Y)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (h₁ : IsZero ((abelianCohomology.{u, u} X ⊤ 1).obj F))
    (h₂ : IsZero ((abelianCohomology.{u, u} Y ⊤ 2).obj ((abelianPushforward.{u, u} f).obj F))) :
    IsZero ((abelianSections.{u, u} Y ⊤).obj
      (((abelianPushforward.{u, u} f).rightDerived 1).obj F)) := by
  have hsurj := abelianSecondEdgeMap_one_surjective f F h₂
  have hsub : Subsingleton ((abelianCohomology.{u, u} X ⊤ 1).obj F) :=
    AddCommGrpCat.subsingleton_of_isZero h₁
  rw [AddCommGrpCat.isZero_iff_subsingleton]
  refine ⟨fun a b => ?_⟩
  obtain ⟨a', rfl⟩ := hsurj a
  obtain ⟨b', rfl⟩ := hsurj b
  rw [Subsingleton.elim a' b']

end Stacks.Cohomology.LerayLowDegree

namespace AlgebraicGeometry

open Stacks.Cohomology.LerayLowDegree

attribute [local instance] abelianSheafHasSheafify

/-! ### Passing between the module-valued and abelian spellings -/

/-- **The vanishing of module-valued cohomology is the vanishing of abelian cohomology**, for
the underlying abelian sheaf ([Stacks, Tag 01F1] part (1)). -/
theorem isZero_rightDerived_evaluation_iff_isZero_abelianCohomology (X : Scheme.{u}) (n : ℕ)
    (M : X.Modules) :
    IsZero (((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).rightDerived n).obj M) ↔
      IsZero ((abelianCohomology.{u, u} X.toTopCat ⊤ n).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)) := by
  have e := (Stacks.Cohomology.ModuleComparison.rightDerivedSectionsForgetIso
    X.ringCatSheaf (⊤ : Opens X) n).app M
  constructor
  · intro h
    exact (Functor.map_isZero
      (forget₂ (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op ⊤))) AddCommGrpCat.{u}) h).of_iso e.symm
  · intro h
    have h' := h.of_iso e
    rw [ModuleCat.isZero_iff_subsingleton]
    exact AddCommGrpCat.isZero_iff_subsingleton.1 h'

/-- A sheaf of modules on a scheme with no nonzero sections over the whole scheme has no nonzero
global sections: a compatible family of sections is determined by its value over `⊤`. -/
theorem subsingleton_sections_of_subsingleton_top {X : Scheme.{u}} (M : X.Modules)
    (h : Subsingleton (M.val.obj (op ⊤))) : Subsingleton M.sections := by
  refine ⟨fun s t => Subtype.ext (funext fun U => ?_)⟩
  have hs := s.2 (homOfLE (le_top : U.unop ≤ ⊤)).op
  have ht := t.2 (homOfLE (le_top : U.unop ≤ ⊤)).op
  rw [← hs, ← ht]
  exact congrArg _ (h.elim (s.1 (op ⊤)) (t.1 (op ⊤)))

/-! ### The comparison `𝒪_X ⟶ g_*𝒪_{X'}` of abelian sheaves -/

/-- **The comparison `𝒪_X ⟶ g_*𝒪_{X'}` of abelian sheaves**, obtained from the comparison `g.c`
of sheaves of rings by forgetting the multiplication. -/
def structureSheafToAbelianPushforward {X' X : Scheme.{u}} (g : X' ⟶ X) :
    (SheafOfModules.toSheaf X.ringCatSheaf).obj (SheafOfModules.unit X.ringCatSheaf) ⟶
      (abelianPushforward.{u, u} g.base).obj
        ((SheafOfModules.toSheaf X'.ringCatSheaf).obj (SheafOfModules.unit X'.ringCatSheaf)) :=
  ⟨Functor.whiskerRight g.c (forget₂ CommRingCat.{u} RingCat.{u} ⋙
    forget₂ RingCat.{u} AddCommGrpCat.{u})⟩

/-- The comparison of abelian sheaves is an isomorphism as soon as `g.c` is. -/
theorem isIso_structureSheafToAbelianPushforward {X' X : Scheme.{u}} (g : X' ⟶ X)
    (hg : IsIso g.c) : IsIso (structureSheafToAbelianPushforward g) := by
  have h : IsIso ((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
      (structureSheafToAbelianPushforward g)) := by
    show IsIso (Functor.whiskerRight g.c (forget₂ CommRingCat.{u} RingCat.{u} ⋙
      forget₂ RingCat.{u} AddCommGrpCat.{u}))
    infer_instance
  exact isIso_of_reflects_iso _ (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

/-! ### `H²(X, 𝒪_X) = 0` -/

/-- **`H²(X, 𝒪_X) = 0` for a normal modification of a two-dimensional local base.** The fibres of
`f : X ⟶ Spec A` have dimension at most one, so [Stacks, Tag 02V7] over the affine base kills
the cohomology of every coherent module in degrees above one. -/
theorem isZero_rightDerived_evaluation_two_of_isModification (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] [IsNormalDomain A] (hdim : ringKrullDim A = 2)
    {X : Scheme.{u}} [IsNormal X] (f : X ⟶ Spec (.of A)) (hf : IsModification f) :
    IsZero (((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).rightDerived 2).obj
      (SheafOfModules.unit X.ringCatSheaf)) := by
  have : IsProper f := hf.isProper
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := AlgebraicGeometry.IsNoetherian.mk
  have : NoetherianSpace (f.fiber (IsLocalRing.closedPoint A)) :=
    (f.fiberHomeo _).isEmbedding.noetherianSpace
  let hfin : Fintype {Z : Set (f.fiber (IsLocalRing.closedPoint A)) //
      Z ∈ irreducibleComponents (f.fiber (IsLocalRing.closedPoint A))} :=
    (NoetherianSpace.finite_irreducibleComponents
      (α := f.fiber (IsLocalRing.closedPoint A))).fintype
  let V : VanishingSituation.{u} :=
    { A := A
      dimension_two := hdim
      X := X
      f := f
      modification := hf
      numberOfComponents := Fintype.card _
      components := (Fintype.equivFin _).symm }
  let S : SemistableReduction.TwoModifications.{u} :=
    { situation := V
      X' := X
      g := 𝟙 X
      modification' := by
        show IsModification (𝟙 X ≫ f)
        rw [Category.id_comp]
        exact hf
      normal := inferInstanceAs (IsNormal X) }
  have hfib : ∀ y : Spec (.of A), topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞) := by
    intro y
    have h := S.topologicalKrullDim_fiber_f'_le_one y
    change topologicalKrullDim ((𝟙 X ≫ f).fiber y) ≤ 1 at h
    rw [Category.id_comp] at h
    exact_mod_cast h
  have : (SheafOfModules.unit X.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
  exact
    Stacks.AlgebraicGeometry.FibreDimension.isZero_rightDerived_moduleGlobalSections_of_affine_base
      f hfib (SheafOfModules.unit X.ringCatSheaf) (p := 2) (by norm_num)

/-! ### The vanishing of `Γ(X, R¹g_*𝒪_{X'})` -/

/-- If `H²(X, 𝒪_X)` vanishes and `g.c` is an isomorphism, then `H²(X, g_*𝒪_{X'})` vanishes in
abelian cohomology. -/
private theorem isZero_abelianCohomology_two_pushforward {X' X : Scheme.{u}} (g : X' ⟶ X)
    (hc : IsIso g.c)
    (h₂ : IsZero (((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).rightDerived 2).obj
      (SheafOfModules.unit X.ringCatSheaf))) :
    IsZero ((abelianCohomology.{u, u} X.toTopCat ⊤ 2).obj
      ((abelianPushforward.{u, u} g.base).obj
        ((SheafOfModules.toSheaf X'.ringCatSheaf).obj (SheafOfModules.unit X'.ringCatSheaf)))) := by
  have := isIso_structureSheafToAbelianPushforward g hc
  exact ((isZero_rightDerived_evaluation_iff_isZero_abelianCohomology X 2 _).1 h₂).of_iso
    ((abelianCohomology.{u, u} X.toTopCat ⊤ 2).mapIso
      (asIso (structureSheafToAbelianPushforward g))).symm

/-- `R¹g_*𝒪_{X'}` has no nonzero global sections once the abelian sections of the abelian
`R¹g_*` of `𝒪_{X'}` vanish. -/
private theorem subsingleton_sections_rightDerived_one_of_isZero_abelianSections
    {X' X : Scheme.{u}} (g : X' ⟶ X)
    (hsec : IsZero ((abelianSections.{u, u} X.toTopCat ⊤).obj
      (((abelianPushforward.{u, u} g.base).rightDerived 1).obj
        ((SheafOfModules.toSheaf X'.ringCatSheaf).obj
          (SheafOfModules.unit X'.ringCatSheaf))))) :
    Subsingleton (((Scheme.Modules.pushforward g).rightDerived 1).obj
      (SheafOfModules.unit X'.ringCatSheaf)).sections := by
  have hmod : IsZero ((abelianSections.{u, u} X.toTopCat ⊤).obj
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj
        (((Scheme.Modules.pushforward g).rightDerived 1).obj
          (SheafOfModules.unit X'.ringCatSheaf)))) :=
    hsec.of_iso ((abelianSections.{u, u} X.toTopCat ⊤).mapIso
      ((Stacks.Cohomology.ModulePushforwardComparison.rightDerived_modulePushforward_forget_iso
        g.toLRSHom.toShHom 1).app (SheafOfModules.unit X'.ringCatSheaf)))
  exact subsingleton_sections_of_subsingleton_top _ (AddCommGrpCat.subsingleton_of_isZero hmod)

/-- **`R¹g_*𝒪_{X'}` has no nonzero global sections** when `H¹(X', 𝒪_{X'}) = 0` and
`H²(X, 𝒪_X) = 0`, for a morphism `g : X' ⟶ X` with `g_*𝒪_{X'} = 𝒪_X`. The second Leray edge map
`H¹(X', 𝒪_{X'}) ⟶ Γ(X, R¹g_*𝒪_{X'})` is onto because `H²(X, g_*𝒪_{X'}) = H²(X, 𝒪_X)` vanishes. -/
theorem subsingleton_sections_rightDerived_one_of_isZero {X' X : Scheme.{u}} (g : X' ⟶ X)
    (hc : IsIso g.c)
    (h₁ : IsZero (((SheafOfModules.evaluation X'.ringCatSheaf (op ⊤)).rightDerived 1).obj
      (SheafOfModules.unit X'.ringCatSheaf)))
    (h₂ : IsZero (((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).rightDerived 2).obj
      (SheafOfModules.unit X.ringCatSheaf))) :
    Subsingleton (((Scheme.Modules.pushforward g).rightDerived 1).obj
      (SheafOfModules.unit X'.ringCatSheaf)).sections := by
  let gR := g.toLRSHom.toShHom
  let FAb := (SheafOfModules.toSheaf X'.ringCatSheaf).obj (SheafOfModules.unit X'.ringCatSheaf)
  have h₁ab : IsZero ((abelianCohomology.{u, u} X'.toTopCat ⊤ 1).obj FAb) :=
    (isZero_rightDerived_evaluation_iff_isZero_abelianCohomology X' 1 _).1 h₁
  exact subsingleton_sections_rightDerived_one_of_isZero_abelianSections g
    (isZero_abelianSections_rightDerived_one_of_isZero gR.hom.base FAb h₁ab
      (isZero_abelianCohomology_two_pushforward g hc h₂))

/-! ### Linearity of the Leray edge map over the global functions -/

/-- Multiplication by a global function, as an endomorphism of the structure sheaf viewed as a
module over itself. -/
def unitSmul (X : Scheme.{u}) (r : Γ(X, ⊤)) :
    SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf :=
  (Stacks.SheafOfModules.terminalSectionToEnd X.ringCatSheaf ⊤ isTerminalTop r).asHom.app _

/-- Taking global sections is linear over the global functions, for the linear structure on
sheaves of modules given by multiplication by global functions. -/
theorem evaluationTop_linear (X : Scheme.{u}) :
    letI : Linear Γ(X, ⊤) (SheafOfModules.{u} X.ringCatSheaf) :=
      Scheme.linearOfRingHom.{u, u} X Γ(X, ⊤) (RingHom.id _)
    letI : Linear Γ(X, ⊤) (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op ⊤))) :=
      inferInstanceAs (Linear Γ(X, ⊤) (ModuleCat.{u} Γ(X, ⊤)))
    Functor.Linear Γ(X, ⊤) (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)) := by
  let : Linear Γ(X, ⊤) (SheafOfModules.{u} X.ringCatSheaf) :=
    Scheme.linearOfRingHom.{u, u} X Γ(X, ⊤) (RingHom.id _)
  let : Linear Γ(X, ⊤) (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op ⊤))) :=
    inferInstanceAs (Linear Γ(X, ⊤) (ModuleCat.{u} Γ(X, ⊤)))
  refine ⟨fun {M N} f r => ?_⟩
  ext x
  exact Scheme.smul_val_app_top X Γ(X, ⊤) (RingHom.id _) r f x

/-- **A global function acts on cohomology through the map induced by multiplying by it.** -/
theorem smul_rightDerived_evaluationTop_eq (X : Scheme.{u}) (n : ℕ) (r : Γ(X, ⊤))
    (x : ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).rightDerived n).obj
      (SheafOfModules.unit X.ringCatSheaf)) :
    (show X.ringCatSheaf.obj.obj (op ⊤) from r) • x =
      (((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).rightDerived n).map
        (unitSmul X r)).hom x := by
  let : Linear Γ(X, ⊤) (SheafOfModules.{u} X.ringCatSheaf) :=
    Scheme.linearOfRingHom.{u, u} X Γ(X, ⊤) (RingHom.id _)
  let : Linear Γ(X, ⊤) (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op ⊤))) :=
    inferInstanceAs (Linear Γ(X, ⊤) (ModuleCat.{u} Γ(X, ⊤)))
  have : Functor.Linear Γ(X, ⊤) (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)) :=
    evaluationTop_linear X
  have := Stacks.DerivedLinear.rightDerived_linear (R := Γ(X, ⊤))
    (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)) n
  have hsmul : unitSmul X r = r • 𝟙 (SheafOfModules.unit X.ringCatSheaf) :=
    (Category.comp_id _).symm
  rw [hsmul, Functor.map_smul, CategoryTheory.Functor.map_id]
  rfl

/-- **`g.c` intertwines multiplication by `r` with multiplication by `g^♯ r`.** -/
theorem unitSmul_comp_structureSheafToAbelianPushforward {X' X : Scheme.{u}} (g : X' ⟶ X)
    (r : Γ(X, ⊤)) :
    (SheafOfModules.toSheaf X.ringCatSheaf).map (unitSmul X r) ≫
        structureSheafToAbelianPushforward g =
      structureSheafToAbelianPushforward g ≫ (abelianPushforward.{u, u} g.base).map
        ((SheafOfModules.toSheaf X'.ringCatSheaf).map (unitSmul X' (g.appTop r))) := by
  ext U s
  show g.c.app U (X.presheaf.map (isTerminalTop.from U.unop).op r *
      (show ↑(X.presheaf.obj U) from s)) =
    X'.presheaf.map (isTerminalTop.from ((Opens.map g.base).obj U.unop)).op (g.appTop r) *
      (show ↑(X'.presheaf.obj (op ((Opens.map g.base).obj U.unop))) from
        g.c.app U (show ↑(X.presheaf.obj U) from s))
  rw [map_mul]
  congr 1
  have h := congrArg (fun k => k r) (g.c.naturality (isTerminalTop.from U.unop).op)
  exact h

/-! ### Modifications between modifications -/

/-- **`f_*𝒪_X = 𝒪_S` for a modification of a normal integral scheme** ([Stacks, Tag 0AY8]). -/
theorem IsModification.isIso_c_of_isNormal_target {S X : Scheme.{u}} [IsIntegral S] [IsNormal S]
    {f : X ⟶ S} (hf : IsModification f) : IsIso f.c := by
  have hX : IsIntegral X := hf.source_isIntegral
  have hP : IsProper f := hf.isProper
  have hfib : IsIso (f.fiberToSpecResidueField (genericPoint S)) :=
    isIso_fiberToSpecResidueField_genericPoint_of_isBirational f hf.isBirational
  have hfibΓ : IsIso (f.fiberToSpecResidueField (genericPoint S)).appTop := by
    have hc0 : IsIso (f.fiberToSpecResidueField (genericPoint S)).c :=
      PresheafedSpace.c_isIso_of_iso (f.fiberToSpecResidueField (genericPoint S)).toPshHom
    exact NatIso.isIso_app_of_isIso _ (Opposite.op ⊤)
  have hΓ : IsIso ((Scheme.ΓSpecIso (S.residueField (genericPoint S))).inv ≫
      (f.fiberToSpecResidueField (genericPoint S)).appTop) := inferInstance
  have hgen : ∀ x : X, x ∈ genericPoints X → f x = genericPoint S := by
    intro x hx
    have hmem := hf.isBirational.bijOn.mapsTo hx
    rwa [genericPoints_eq_singleton, Set.mem_singleton_iff] at hmem
  exact Stacks.SteinFactorization.isIso_c_of_isNormal f hgen hΓ

/-! ### The Leray edge map on module-valued cohomology -/

/-- The first cohomology `H¹(X, 𝒪_X)` of the structure sheaf, as a module over `Γ(X, 𝒪_X)`. -/
abbrev structureSheafH1 (X : Scheme.{u}) : ModuleCat.{u} (X.ringCatSheaf.obj.obj (op ⊤)) :=
  ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).rightDerived 1).obj
    (SheafOfModules.unit X.ringCatSheaf)

/-- The comparison of `H¹(X, 𝒪_X)` with the abelian-sheaf cohomology of `𝒪_X`
([Stacks, Tag 01F1] part (1)). -/
abbrev structureSheafH1ForgetIso (X : Scheme.{u}) :
    (forget₂ (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op ⊤))) AddCommGrpCat.{u}).obj
        (structureSheafH1 X) ≅
      (abelianCohomology.{u, u} X.toTopCat ⊤ 1).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj (SheafOfModules.unit X.ringCatSheaf)) :=
  (Stacks.Cohomology.ModuleComparison.rightDerivedSectionsForgetIso
    X.ringCatSheaf (⊤ : Opens X) 1).app (SheafOfModules.unit X.ringCatSheaf)

/-- **The Leray edge map `H¹(X, 𝒪_X) ⟶ H¹(X', 𝒪_{X'})`** of `g : X' ⟶ X`, as a morphism of
abelian groups: `𝒪_X ⟶ g_*𝒪_{X'}` on cohomology followed by the first edge map. -/
def leraySmulEdge {X' X : Scheme.{u}} (g : X' ⟶ X) :
    (forget₂ (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op ⊤))) AddCommGrpCat.{u}).obj
        (structureSheafH1 X) ⟶
      (forget₂ (ModuleCat.{u} (X'.ringCatSheaf.obj.obj (op ⊤))) AddCommGrpCat.{u}).obj
        (structureSheafH1 X') :=
  (structureSheafH1ForgetIso X).hom ≫
    (abelianCohomology.{u, u} X.toTopCat ⊤ 1).map (structureSheafToAbelianPushforward g) ≫
      (abelianEdgeMap.{u, u} g.base 1).app
        ((SheafOfModules.toSheaf X'.ringCatSheaf).obj (SheafOfModules.unit X'.ringCatSheaf)) ≫
        (structureSheafH1ForgetIso X').inv

/-- **The edge map intertwines multiplication by `r` and by `g^♯ r`**, as morphisms. -/
theorem leraySmulEdge_naturality {X' X : Scheme.{u}} (g : X' ⟶ X) (r : Γ(X, ⊤)) :
    (forget₂ (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op ⊤))) AddCommGrpCat.{u}).map
        (((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).rightDerived 1).map
          (unitSmul X r)) ≫ leraySmulEdge g =
      leraySmulEdge g ≫
        (forget₂ (ModuleCat.{u} (X'.ringCatSheaf.obj.obj (op ⊤))) AddCommGrpCat.{u}).map
          (((SheafOfModules.evaluation X'.ringCatSheaf (op ⊤)).rightDerived 1).map
            (unitSmul X' (g.appTop r))) := by
  have e₁ := (Stacks.Cohomology.ModuleComparison.rightDerivedSectionsForgetIso
    X.ringCatSheaf (⊤ : Opens X) 1).hom.naturality (unitSmul X r)
  have e₂ := (Stacks.Cohomology.ModuleComparison.rightDerivedSectionsForgetIso
    X'.ringCatSheaf (⊤ : Opens X') 1).inv.naturality (unitSmul X' (g.appTop r))
  have e₃ : (abelianCohomology.{u, u} X.toTopCat ⊤ 1).map ((abelianPushforward.{u, u} g.base).map
        ((SheafOfModules.toSheaf X'.ringCatSheaf).map (unitSmul X' (g.appTop r)))) ≫
      (abelianEdgeMap.{u, u} g.base 1).app
        ((SheafOfModules.toSheaf X'.ringCatSheaf).obj (SheafOfModules.unit X'.ringCatSheaf)) =
      (abelianEdgeMap.{u, u} g.base 1).app
        ((SheafOfModules.toSheaf X'.ringCatSheaf).obj (SheafOfModules.unit X'.ringCatSheaf)) ≫
      (abelianCohomology.{u, u} X'.toTopCat ⊤ 1).map
        ((SheafOfModules.toSheaf X'.ringCatSheaf).map (unitSmul X' (g.appTop r))) :=
    (abelianEdgeMap.{u, u} g.base 1).naturality
      ((SheafOfModules.toSheaf X'.ringCatSheaf).map (unitSmul X' (g.appTop r)))
  have e₄ := congrArg (fun k => (abelianCohomology.{u, u} X.toTopCat ⊤ 1).map k)
    (unitSmul_comp_structureSheafToAbelianPushforward g r)
  simp only [Functor.map_comp] at e₄
  dsimp only [Functor.comp_map] at e₁ e₂
  rw [show (((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (op ⊤)).rightDerived 1).map ((SheafOfModules.toSheaf X.ringCatSheaf).map (unitSmul X r)) =
      (abelianCohomology.{u, u} X.toTopCat ⊤ 1).map
        ((SheafOfModules.toSheaf X.ringCatSheaf).map (unitSmul X r)) from rfl] at e₁
  rw [show (((sheafSections (Opens.grothendieckTopology X') AddCommGrpCat.{u}).obj
      (op ⊤)).rightDerived 1).map
        ((SheafOfModules.toSheaf X'.ringCatSheaf).map (unitSmul X' (g.appTop r))) =
      (abelianCohomology.{u, u} X'.toTopCat ⊤ 1).map
        ((SheafOfModules.toSheaf X'.ringCatSheaf).map (unitSmul X' (g.appTop r))) from rfl] at e₂
  simp only [leraySmulEdge, structureSheafH1ForgetIso, Iso.app_hom, Iso.app_inv,
    ← Category.assoc]
  rw [e₁]
  simp only [Category.assoc]
  rw [reassoc_of% e₄]
  rw [reassoc_of% e₃]
  rw [e₂]

/-- **The Leray edge map `H¹(X, 𝒪_X) ⟶ H¹(X', 𝒪_{X'})` is injective** when `g_*𝒪_{X'} = 𝒪_X`. -/
theorem leraySmulEdge_injective {X' X : Scheme.{u}} (g : X' ⟶ X) (hc : IsIso g.c) :
    Function.Injective (leraySmulEdge g) := by
  have := isIso_structureSheafToAbelianPushforward g hc
  have hinj := abelianEdgeMap_injective.{u, u} g.base
    ((SheafOfModules.toSheaf X'.ringCatSheaf).obj (SheafOfModules.unit X'.ringCatSheaf))
  have h1 : Function.Injective (structureSheafH1ForgetIso X).hom :=
    ((AddCommGrpCat.mono_iff_injective _).1 inferInstance)
  have h2 : Function.Injective ((abelianCohomology.{u, u} X.toTopCat ⊤ 1).map
      (structureSheafToAbelianPushforward g)) :=
    ((AddCommGrpCat.mono_iff_injective _).1 inferInstance)
  have h4 : Function.Injective (structureSheafH1ForgetIso X').inv :=
    ((AddCommGrpCat.mono_iff_injective _).1 inferInstance)
  intro a b hab
  exact h1 (h2 (hinj (h4 hab)))

/-- **If the Leray edge map is onto and `H²(X, 𝒪_X) = 0`, then `Γ(X, R¹g_*𝒪_{X'}) = 0`.** The
second edge map kills the image of the first and is onto. -/
theorem subsingleton_sections_of_leraySmulEdge_surjective {X' X : Scheme.{u}} (g : X' ⟶ X)
    (hc : IsIso g.c) (hsurj : Function.Surjective (leraySmulEdge g))
    (h₂ : IsZero (((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).rightDerived 2).obj
      (SheafOfModules.unit X.ringCatSheaf))) :
    Subsingleton (((Scheme.Modules.pushforward g).rightDerived 1).obj
      (SheafOfModules.unit X'.ringCatSheaf)).sections := by
  let FAb := (SheafOfModules.toSheaf X'.ringCatSheaf).obj (SheafOfModules.unit X'.ringCatSheaf)
  have := isIso_structureSheafToAbelianPushforward g hc
  have hsec2 := abelianSecondEdgeMap_one_surjective g.base FAb
    (isZero_abelianCohomology_two_pushforward g hc h₂)
  -- the first edge map is onto
  have hedge : Function.Surjective ((abelianEdgeMap.{u, u} g.base 1).app FAb) := by
    intro y
    obtain ⟨x, hx⟩ := hsurj ((structureSheafH1ForgetIso X').inv y)
    refine ⟨(abelianCohomology.{u, u} X.toTopCat ⊤ 1).map (structureSheafToAbelianPushforward g)
      ((structureSheafH1ForgetIso X).hom x), ?_⟩
    have h4 : Function.Injective (structureSheafH1ForgetIso X').inv :=
      ((AddCommGrpCat.mono_iff_injective _).1 inferInstance)
    exact h4 hx
  have hsec : IsZero ((abelianSections.{u, u} X.toTopCat ⊤).obj
      (((abelianPushforward.{u, u} g.base).rightDerived 1).obj FAb)) := by
    rw [AddCommGrpCat.isZero_iff_subsingleton]
    refine ⟨fun a b => ?_⟩
    obtain ⟨a', rfl⟩ := hsec2 a
    obtain ⟨b', rfl⟩ := hsec2 b
    obtain ⟨a'', rfl⟩ := hedge a'
    obtain ⟨b'', rfl⟩ := hedge b'
    have hz := abelianEdgeMap_comp_abelianSecondEdgeMap.{u, u} g.base FAb
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, hz]
    rfl
  exact subsingleton_sections_rightDerived_one_of_isZero_abelianSections g hsec

/-- The ring map `A ⟶ Γ(X, 𝒪_X)` of a scheme over `Spec A`, as used by
`AlgebraicGeometry.firstCohomologyAsBaseModule`. -/
abbrev baseToGlobal {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) :
    A →+* X.ringCatSheaf.obj.obj (op ⊤) :=
  ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom

/-- **The Leray edge map is semilinear along `g^♯ : Γ(X, 𝒪_X) ⟶ Γ(X', 𝒪_{X'})`.** -/
theorem leraySmulEdge_smul {X' X : Scheme.{u}} (g : X' ⟶ X)
    (r : Γ(X, ⊤)) (x : ↑(structureSheafH1 X)) :
    leraySmulEdge g ((show X.ringCatSheaf.obj.obj (op ⊤) from r) • x) =
      (show X'.ringCatSheaf.obj.obj (op ⊤) from g.appTop r) •
        (show ↑(structureSheafH1 X') from leraySmulEdge g x) := by
  rw [smul_rightDerived_evaluationTop_eq X 1 r x,
    smul_rightDerived_evaluationTop_eq X' 1 (g.appTop r)]
  have h := ConcreteCategory.congr_hom (leraySmulEdge_naturality g r) x
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  exact h

/-- **The Leray edge map as an `A`-linear map** `H¹(X, 𝒪_X) ⟶ H¹(X', 𝒪_{X'})` of schemes over
`Spec A`. -/
def lerayEdgeLinearMap {A : Type u} [CommRing A] {X' X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (g : X' ⟶ X) :
    firstCohomologyAsBaseModule X f →ₗ[A] firstCohomologyAsBaseModule X' (g ≫ f) where
  toFun x := leraySmulEdge g x
  map_add' x y := map_add (leraySmulEdge g).hom x y
  map_smul' a x := by
    have hg : baseToGlobal (g ≫ f) a = g.appTop (baseToGlobal f a) := by
      rw [baseToGlobal, baseToGlobal, Scheme.Hom.comp_appTop]
      rfl
    have h := leraySmulEdge_smul g (baseToGlobal f a) x
    rw [← hg] at h
    exact h

end AlgebraicGeometry

end
