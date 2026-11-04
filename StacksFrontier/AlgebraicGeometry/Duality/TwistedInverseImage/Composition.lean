module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.Basic

/-!
# The twisted inverse image of a composite

Let `g : Z ⟶ X` and `f : X ⟶ Y` be morphisms of schemes along which derived direct image
preserves quasi-coherence of cohomology, and suppose the restricted derived direct images have
right adjoints `a_g`, `a_f` and `a_{g ≫ f}` (the twisted inverse images of [Stacks, Tag 0A9E]).
Derived direct image is compatible with composition, `R(g ≫ f)_* ≅ Rf_* ∘ Rg_*`, so taking right
adjoints gives

  `a_{g ≫ f} ≅ a_g ∘ a_f`.

## Main definitions

* `Stacks.Duality.quasiCoherentDerivedPushforwardCompIso` — the composition formula for derived
  direct image on the quasi-coherent derived categories.
* `Stacks.Duality.twistedInverseImageCompIso` — the composition formula for the twisted inverse
  image.
* `Stacks.Duality.twistedInverseImageIsoOfIsIso` — the twisted inverse image of an isomorphism
  `e` is derived direct image along `e⁻¹`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u

namespace Stacks.Duality

variable {Z X Y : Scheme.{u}} (g : Z ⟶ X) (f : X ⟶ Y)
  (hpushg : ∀ (K : quasiCoherentDerivedCategory Z) (i : ℤ),
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((derivedPushforward g).obj K.obj)).IsQuasicoherent)
  (hpushf : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
  (hpushgf : ∀ (K : quasiCoherentDerivedCategory Z) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward (g ≫ f)).obj K.obj)).IsQuasicoherent)

/-- **Derived direct image of a composite on the quasi-coherent derived categories**:
`Rg_* ⋙ Rf_* ≅ R(g ≫ f)_*`, the ambient composition formula
`Stacks.Duality.derivedPushforwardCompIso` read on the full subcategories. -/
def quasiCoherentDerivedPushforwardCompIso :
    quasiCoherentDerivedPushforward g hpushg ⋙ quasiCoherentDerivedPushforward f hpushf ≅
      quasiCoherentDerivedPushforward (g ≫ f) hpushgf :=
  NatIso.ofComponents
    (fun K => ObjectProperty.isoMk _ ((derivedPushforwardCompIso g f).app K.obj))
    fun e => ObjectProperty.hom_ext _ ((derivedPushforwardCompIso g f).hom.naturality e.hom)

/-- The component of `quasiCoherentDerivedPushforwardCompIso` at `K` is the component at `K.obj`
of `Stacks.Duality.derivedPushforwardCompIso`. -/
@[simp]
theorem quasiCoherentDerivedPushforwardCompIso_hom_app_hom (K : quasiCoherentDerivedCategory Z) :
    ((quasiCoherentDerivedPushforwardCompIso g f hpushg hpushf hpushgf).hom.app K).hom =
      (derivedPushforwardCompIso g f).hom.app K.obj :=
  rfl

variable [(quasiCoherentDerivedPushforward g hpushg).IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward f hpushf).IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward (g ≫ f) hpushgf).IsLeftAdjoint]

/-- **The twisted inverse image of a composite is the composite of the twisted inverse images**,
`a_{g ≫ f} ≅ a_f ⋙ a_g`, as right adjoints of `R(g ≫ f)_* ≅ Rg_* ⋙ Rf_*`. -/
def twistedInverseImageCompIso :
    twistedInverseImage (g ≫ f) hpushgf ≅
      twistedInverseImage f hpushf ⋙ twistedInverseImage g hpushg :=
  Adjunction.rightAdjointUniq (twistedInverseImageAdjunction (g ≫ f) hpushgf)
    (((twistedInverseImageAdjunction g hpushg).comp
      (twistedInverseImageAdjunction f hpushf)).ofNatIsoLeft
        (quasiCoherentDerivedPushforwardCompIso g f hpushg hpushf hpushgf))

/-! ### Isomorphisms -/

section Iso

variable {X Y : Scheme.{u}}

/-- Derived direct image on `D_QCoh` along equal morphisms: the two functors are isomorphic. -/
def quasiCoherentDerivedPushforwardCongr {f g : X ⟶ Y} (h : f = g)
    (hf : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
    (hg : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((derivedPushforward g).obj K.obj)).IsQuasicoherent) :
    quasiCoherentDerivedPushforward f hf ≅ quasiCoherentDerivedPushforward g hg := by
  subst h
  exact Iso.refl _

variable (e : X ⟶ Y) [IsIso e]
  (hpushe : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward e).obj K.obj)).IsQuasicoherent)
  (hpushinv : ∀ (K : quasiCoherentDerivedCategory Y) (i : ℤ),
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((derivedPushforward (inv e)).obj K.obj)).IsQuasicoherent)
  (hidX : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((derivedPushforward (𝟙 X)).obj K.obj)).IsQuasicoherent)
  (hidY : ∀ (K : quasiCoherentDerivedCategory Y) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward (𝟙 Y)).obj K.obj)).IsQuasicoherent)

/-- **Derived direct image along an isomorphism is an equivalence of the quasi-coherent derived
categories**, with quasi-inverse derived direct image along the inverse. -/
def quasiCoherentDerivedPushforwardEquivalenceOfIsIso :
    quasiCoherentDerivedCategory X ≌ quasiCoherentDerivedCategory Y :=
  have h₁ : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor X.Modules i).obj
        ((derivedPushforward (e ≫ inv e)).obj K.obj)).IsQuasicoherent := by
    rw [IsIso.hom_inv_id]; exact hidX
  have h₂ : ∀ (K : quasiCoherentDerivedCategory Y) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((derivedPushforward (inv e ≫ e)).obj K.obj)).IsQuasicoherent := by
    rw [IsIso.inv_hom_id]; exact hidY
  CategoryTheory.Equivalence.mk (quasiCoherentDerivedPushforward e hpushe)
    (quasiCoherentDerivedPushforward (inv e) hpushinv)
    ((quasiCoherentDerivedPushforwardIdIso X hidX).symm ≪≫
      quasiCoherentDerivedPushforwardCongr (IsIso.hom_inv_id e).symm hidX h₁ ≪≫
      (quasiCoherentDerivedPushforwardCompIso e (inv e) hpushe hpushinv h₁).symm)
    (quasiCoherentDerivedPushforwardCompIso (inv e) e hpushinv hpushe h₂ ≪≫
      quasiCoherentDerivedPushforwardCongr (IsIso.inv_hom_id e) h₂ hidY ≪≫
      quasiCoherentDerivedPushforwardIdIso Y hidY)

/-- The twisted inverse images along equal morphisms are isomorphic. -/
def twistedInverseImageCongr {f g : X ⟶ Y} (h : f = g)
    (hf : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
    (hg : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((derivedPushforward g).obj K.obj)).IsQuasicoherent)
    [(quasiCoherentDerivedPushforward f hf).IsLeftAdjoint]
    [(quasiCoherentDerivedPushforward g hg).IsLeftAdjoint] :
    twistedInverseImage f hf ≅ twistedInverseImage g hg := by
  subst h
  exact Iso.refl _

variable [(quasiCoherentDerivedPushforward e hpushe).IsLeftAdjoint]

/-- **The twisted inverse image of an isomorphism `e` is derived direct image along `e⁻¹`**. -/
def twistedInverseImageIsoOfIsIso :
    twistedInverseImage e hpushe ≅ quasiCoherentDerivedPushforward (inv e) hpushinv :=
  Adjunction.rightAdjointUniq (twistedInverseImageAdjunction e hpushe)
    (quasiCoherentDerivedPushforwardEquivalenceOfIsIso e hpushe hpushinv hidX hidY).toAdjunction

end Iso

end Stacks.Duality
