module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Retract
public import StacksCore.CategoryTheory.IsFinitelyPresentable
import StacksCore.Tactic.StacksAttribute
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomFilteredColimitSections
import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
import StacksFrontier.AlgebraicGeometry.Modules.FinitePresentationFromAffine
import StacksFrontier.AlgebraicGeometry.QuasiCoherent.FinitePresentationColimit
import StacksFrontier.RingTheory.Module.Finiteness.HomColimit
import StacksFrontier.Topology.Sheaves.Limits.SpectralCovers

/-!
# Categorically compact quasi-coherent modules

Let `X` be a quasi-compact and quasi-separated scheme.  A quasi-coherent `𝒪_X`-module is a
categorically compact object of the category `QCoh(𝒪_X)` of quasi-coherent modules — that is, a
finitely presentable object in the sense of `CategoryTheory.IsFinitelyPresentable` — if and only
if it is of finite presentation as a sheaf of modules.

Both implications come from the two colimit descriptions available on such a scheme.  A module of
finite presentation is compact already in the category of *all* `𝒪_X`-modules, because `Hom(F, -)`
commutes with filtered colimits there [Stacks, Tag 01BS]; quasi-coherence being stable under
colimits, the inclusion of `QCoh(𝒪_X)` creates filtered colimits, so compactness descends to the
subcategory.  Conversely a quasi-coherent module is a directed colimit of finitely presented
quasi-coherent modules [Stacks, Tag 01PK], and compactness factors the identity through one stage
of that colimit, exhibiting the module as a direct summand of a finitely presented one; a direct
summand is again of finite presentation, which is checked on the sections over the affine opens.

## Main results

* `AlgebraicGeometry.isFinitelyPresentable_iff_isFinitePresentation`: **[Stacks, Tag 0GPE]** on a
  quasi-compact and quasi-separated scheme, the categorically compact objects of `QCoh(𝒪_X)` are
  exactly the modules of finite presentation.

## Implementation notes

`QCoh(𝒪_X)` is the full subcategory of `SheafOfModules X.ringCatSheaf` cut out by the object
property `SheafOfModules.isQuasicoherent X.ringCatSheaf`, so compactness is
`CategoryTheory.IsFinitelyPresentable` for that category while finite presentation is a property
of the underlying sheaf of modules.

A retract of modules is turned into finite presentation of the sections over an affine open rather
than into finite presentation of the sheaf directly: the module of sections of the ambient sheaf
over an affine open is finitely presented by
`Stacks.AlgebraicGeometry.FinitePresentationLocal.finitePresentation_sections_of_restrict`, a
retract of modules is inherited by sections, and
`Stacks.AlgebraicGeometry.FinitePresentationLocal.isFinitePresentation_of_affineCover` assembles
the affine opens back into the sheaf.

## References

* [Stacks Project, Tag 0GPE](https://stacks.math.columbia.edu/tag/0GPE)
* [Stacks Project, Tag 01BS](https://stacks.math.columbia.edu/tag/01BS)
* [Stacks Project, Tag 01PK](https://stacks.math.columbia.edu/tag/01PK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules TopologicalSpace

universe u

namespace AlgebraicGeometry

/- `AlgebraicGeometry.Scheme.Modules` is a plain definition for `SheafOfModules X.ringCatSheaf`
carrying its own `Category` instance, whose `Hom` field is
`AlgebraicGeometry.Scheme.Modules.Hom` rather than `SheafOfModules.Hom`.  The two categories are
definitionally equal but not syntactically, so instance search — being syntactic — does not
transport a statement about the quasi-coherent modules, which is phrased in
`SheafOfModules X.ringCatSheaf`, to the corresponding statement about `𝒪_X`-modules.  Making the
three definitions implicitly reducible is the repo's idiom for this. -/
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.Modules.Hom AlgebraicGeometry.Scheme.Modules.instCategory

variable {X : Scheme.{u}}

/-! ### Finite presentation of a direct summand -/

/-- The map on sections over an open induced by a morphism of `𝒪_X`-modules, as a linear map over
the commutative ring `Γ(X, U)` of functions on that open. -/
private def sectionsLinearMap {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens) :
    Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) where
  toFun := Scheme.Modules.Hom.app φ U
  map_add' a b := map_add _ a b
  map_smul' c a := Scheme.Modules.Hom.app_smul φ c a

/-- **The sections of a direct summand over an open are a direct summand of the sections.**  A
retract in the category of `𝒪_X`-modules is carried to a retract of `Γ(X, U)`-modules by taking
sections over `U`, so finite presentation of the sections of the ambient module descends. -/
private lemma finitePresentation_sections_of_retract {M N : X.Modules} (h : Retract M N)
    (U : X.Opens) [Module.FinitePresentation Γ(X, U) Γ(N, U)] :
    Module.FinitePresentation Γ(X, U) Γ(M, U) := by
  refine Module.FinitePresentation.of_retract (sectionsLinearMap h.i U)
    (sectionsLinearMap h.r U) ?_
  ext x
  change (Scheme.Modules.Hom.app h.r U) ((Scheme.Modules.Hom.app h.i U) x) = x
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, h.retract,
    Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply]

/-- **A direct summand of a module of finite presentation is of finite presentation.**  The
summand is quasi-coherent, so finite presentation may be checked on the sections over the affine
opens, where it is inherited from the ambient module. -/
private lemma isFinitePresentation_of_retract {M N : X.Modules} (h : Retract M N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] [N.IsFinitePresentation] :
    M.IsFinitePresentation := by
  refine Stacks.AlgebraicGeometry.FinitePresentationLocal.isFinitePresentation_of_affineCover
    M (fun V : X.affineOpens => (V : X.Opens)) (IsOpenCover.mk (iSup_affineOpens_eq_top X))
    (fun V => V.2) fun V => ?_
  have hN : Module.FinitePresentation Γ(X, (V : X.Opens)) Γ(N, (V : X.Opens)) :=
    Stacks.AlgebraicGeometry.FinitePresentationLocal.finitePresentation_sections_of_restrict
      N V.2 (Stacks.AlgebraicGeometry.FinitePresentationLocal.isFinitePresentation_restrict
        (V : X.Opens).ι N inferInstance)
  exact finitePresentation_sections_of_retract h (V : X.Opens)

/-! ### Compactness in the category of quasi-coherent modules -/

/-- Morphisms out of a quasi-coherent module in the category of quasi-coherent modules are the
morphisms out of it in the category of all `𝒪_X`-modules: the covariant Hom functor on
`QCoh(𝒪_X)` is the restriction along the inclusion of the covariant Hom functor on
`𝒪_X`-modules. -/
private def coyonedaIsoιCompCoyoneda (X : Scheme.{u})
    (M : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    coyoneda.obj (op M) ≅
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ⋙ coyoneda.obj (op M.obj) :=
  NatIso.ofComponents
    (fun _ => Equiv.toIso
      { toFun := fun f => f.hom
        invFun := fun f => ObjectProperty.homMk f
        left_inv := fun _ => ObjectProperty.hom_ext _ rfl
        right_inv := fun _ => rfl })
    (fun _ => by ext; rfl)

/-- A quasi-compact and quasi-separated scheme has a cofinal system of finite open coverings with
quasi-compact pairwise intersections, which is hypothesis (3) of [Stacks, Tag 01BS]. -/
private lemma hasFiniteCompactCofinalCovers_top (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] :
    DirectedColimitOfSheaves.HasFiniteCompactCofinalCovers (X := TopCat.of X) ⊤ := by
  let : PrespectralSpace (TopCat.of X) := inferInstanceAs (PrespectralSpace X)
  let : QuasiSeparatedSpace (TopCat.of X) := inferInstanceAs (QuasiSeparatedSpace X)
  have hcompact : IsCompact (Set.univ : Set (X : Type u)) := isCompact_univ
  intro J V hVU hcov
  exact hasFiniteCompactCofinalCovers_of_isCompact (X := TopCat.of X) ⊤ hcompact V hVU hcov

/-- **Stacks Project, Tag 0GPE.**  A quasi-coherent module on a quasi-compact and quasi-separated
scheme is a categorically compact object of the category of quasi-coherent modules if and only if
it is of finite presentation. -/
@[stacks 0GPE]
theorem isFinitelyPresentable_iff_isFinitePresentation
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    IsFinitelyPresentable.{u} F ↔ F.obj.IsFinitePresentation := by
  let Q := SheafOfModules.isQuasicoherent X.ringCatSheaf
  constructor
  · intro h
    obtain ⟨I, hI, hInh, hDir, D, φ, hfp, ⟨hc⟩⟩ :=
      exists_directed_system_of_isFinitePresentation X F.obj
    let Dq : I ⥤ Q.FullSubcategory := Q.lift D fun i => by
      let : (D.obj i).IsFinitePresentation := hfp i
      infer_instance
    let ψ : Dq ⟶ (Functor.const I).obj F :=
      { app := fun i => ObjectProperty.homMk (φ.app i)
        naturality := fun _ _ f => ObjectProperty.hom_ext _ (NatTrans.naturality φ f) }
    have hcq : IsColimit (Cocone.mk F ψ) :=
      isColimitOfReflects Q.ι
        (IsColimit.ofIsoColimit hc (Cocone.ext (Iso.refl _) fun _ => by simp [Dq, ψ, Q]))
    obtain ⟨i, p, hp⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hcq (𝟙 F)
    let : (D.obj i).IsFinitePresentation := hfp i
    have hret : Retract F.obj (D.obj i) :=
      Retract.map (⟨p, ψ.app i, hp⟩ : Retract F (Dq.obj i)) Q.ι
    exact isFinitePresentation_of_retract hret
  · intro _
    have : PreservesFilteredColimitsOfSize.{u, u} (coyoneda.obj (op F.obj)) :=
      ⟨fun J _ _ =>
        Stacks.SheafOfModules.preservesColimitsOfShape_coyoneda_of_isFinitePresentation
          X.sheaf F.obj J (hasFiniteCompactCofinalCovers_top X)⟩
    have : PreservesFilteredColimitsOfSize.{u, u} Q.ι := ⟨fun J _ _ => by
      let : Q.IsClosedUnderColimitsOfShape J :=
        Stacks.AlgebraicGeometry.QuasicoherentColimits.isClosedUnderColimitsOfShape X
      let : CreatesColimitsOfShape J Q.ι := inferInstance
      infer_instance⟩
    exact isFinitelyPresentable_iff_preservesFilteredColimitsOfSize.mpr ⟨fun J _ _ =>
      preservesColimitsOfShape_of_natIso (coyonedaIsoιCompCoyoneda X F).symm⟩

end AlgebraicGeometry

end
