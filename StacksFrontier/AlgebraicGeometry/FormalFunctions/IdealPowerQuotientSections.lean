module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import StacksFrontier.AlgebraicGeometry.ModuleGlobalSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SectionsComplete
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.PrincipalPowerSubscheme

/-!
# Global sections of `𝒪_Z / 𝓘 ⁿ 𝒪_Z` are the functions on the closed subscheme of `𝓘 ⁿ`

Let `Z` be a scheme and `𝓘` a quasi-coherent ideal sheaf on `Z`.  The quotient
`𝒪_Z / 𝓘 ⁿ 𝒪_Z` of `Stacks.Algebraization.idealPowerQuotient` and the closed subscheme
`(𝓘 ^ n).subscheme` cut out by `𝓘 ^ n` are two descriptions of the same object, and this file
identifies them on global sections: `Γ(Z, 𝒪_Z / 𝓘 ⁿ 𝒪_Z)` is the ring `Γ((𝓘 ^ n).subscheme, ⊤)`
of functions on that subscheme, as a module over `Γ(Z, ⊤)`.

The identification is natural in `n` — lowering the exponent corresponds to restricting functions
along the closed immersion `(𝓘 ^ n).subscheme ⟶ (𝓘 ^ m).subscheme` of `n ≤ m` — and it carries
the quotient projection `𝒪_Z ⟶ 𝒪_Z / 𝓘 ⁿ 𝒪_Z` to the restriction of functions
`Γ(Z, ⊤) ⟶ Γ((𝓘 ^ n).subscheme, ⊤)` along `(𝓘 ^ n).subschemeι`.  Those two compatibilities pin
the family of isomorphisms down.

Everything is stated for an arbitrary quasi-coherent ideal sheaf and specialized at the end to
the ideal sheaf `I · 𝒪_Z` of an ideal `I` of an affine base, which is the form the theorem on
formal functions uses.  No properness, Noetherian or finiteness hypothesis enters.

## Main definitions

* `Stacks.Cohomology.FormalFunctions.moduleGlobalSectionsRightDerivedZeroIso` — the degree-zero
  right derived functor of `Γ(Z, -)` on sheaves of modules is `Γ(Z, -)`.
* `Stacks.Cohomology.FormalFunctions.pushforwardUnitComparison` — for a factorization
  `j ≫ w = v` of morphisms of schemes, the comparison `w_* 𝒪_W ⟶ v_* 𝒪_V`, which on global
  sections is restriction of functions along `j`.
* `Stacks.Cohomology.FormalFunctions.idealPowerQuotientSubschemeIso` — the sheaf-level
  identification `𝒪_Z / 𝓘 ⁿ 𝒪_Z ≅ (ι_n)_* 𝒪_{(𝓘 ^ n).subscheme}`.
* `Stacks.Cohomology.FormalFunctions.idealPowerQuotientSubschemeDrop` — the map
  `(ι_m)_* 𝒪_{(𝓘 ^ m).subscheme} ⟶ (ι_n)_* 𝒪_{(𝓘 ^ n).subscheme}` for `n ≤ m`.
* `Stacks.Cohomology.FormalFunctions.idealPowerQuotientSubschemeSectionsIso` and its
  specialization `Stacks.Cohomology.FormalFunctions.idealPowerQuotientSectionsIso` — the
  resulting isomorphism of `Γ(Z, ⊤)`-modules
  `Γ(Z, 𝒪_Z / 𝓘 ⁿ 𝒪_Z) ≅ Γ((𝓘 ^ n).subscheme, ⊤)`.
* `Stacks.Cohomology.FormalFunctions.idealPowerSubschemeIsoPullback` — for the ideal sheaf of an
  ideal `I` of an affine base, that subscheme is `Z ×_{Spec A} Spec (A / I ^ n)`.

## Main results

* `Stacks.Cohomology.FormalFunctions.cokernel_π_comp_idealPowerQuotientSubschemeIso_hom` and
  `Stacks.Cohomology.FormalFunctions.idealPowerQuotientSubschemeSectionsIso_hom_app_top_π` —
  **compatibility with the quotient projection**: the composite
  `Γ(Z, ⊤) ⟶ Γ(Z, 𝒪_Z / 𝓘 ⁿ 𝒪_Z) ≅ Γ((𝓘 ^ n).subscheme, ⊤)` is restriction of functions along
  `(𝓘 ^ n).subschemeι`.
* `Stacks.Cohomology.FormalFunctions.idealPowerQuotientSubschemeIso_naturality` and
  `Stacks.Cohomology.FormalFunctions.idealPowerQuotientSubschemeSectionsIso_hom_app_top_drop` —
  **naturality in `n`**: the exponent-lowering map
  `Stacks.Algebraization.idealPowerQuotientDrop` corresponds to restriction of functions along
  `Scheme.IdealSheafData.inclusion`.

## Implementation notes

The identification is **not** constructed on sections.  It is the global sections of a sheaf-level
isomorphism: [Stacks, Tag 0EL1] in the form
`Stacks.Algebraization.idealQuotientPushforwardIso`, applied to the closed immersion
`(𝓘 ^ n).subschemeι` — whose ideal sheaf is `𝓘 ^ n` by
`AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι` — at the structure sheaf, followed by
`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`, which says that the restriction of the
structure sheaf to the subscheme is the structure sheaf of the subscheme.  Both squares are
therefore proved at sheaf level, where the quotient projection is an epimorphism and
`Stacks.Algebraization.idealQuotientPushforwardMap_π` normalizes the comparison by the adjunction
unit; `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_homEquiv` then turns the unit into
`AlgebraicGeometry.Scheme.Modules.unitToPushforwardUnit`, which acts on sections by restriction
of functions.

`Stacks.Cohomology.FormalFunctions.moduleGlobalSectionsRightDerivedZeroIso` is nothing but
Mathlib's `CategoryTheory.Functor.rightDerivedZeroIsoSelf` at `Γ(Z, -)`; it is named here only
because the library otherwise has no name for it.  The instance it needs,
`AlgebraicGeometry.moduleGlobalSections_preservesFiniteLimits`, is already in
`StacksFrontier/AlgebraicGeometry/ModuleGlobalSections.lean`, so nothing has to be reproved.

`(AlgebraicGeometry.moduleGlobalSections Z).obj ((Scheme.Modules.pushforward v).obj
(Scheme.unitModule W))` is *definitionally* `ModuleCat.of Γ(Z, ⊤) Γ(W, ⊤)` for the
`Γ(Z, ⊤)`-action obtained from `Module.compHom` along `v.appTop`: the module of sections of a
pushforward over `U` is the module of sections over `v ⁻¹ᵁ U`, and `v ⁻¹ᵁ ⊤` is `⊤`.  So the
isomorphism of modules of global sections is literally `Γ(Z, -)` applied to the sheaf-level
isomorphism, and no transport of scalars is needed; the `Module Γ(Z, ⊤) Γ(W, ⊤)` instance is
produced inside the statement with `letI`, since it is not an instance of the library.

The comparison `pushforwardUnitComparison` is built from
`AlgebraicGeometry.Scheme.Modules.unitToPushforwardUnit` and
`AlgebraicGeometry.Scheme.Modules.pushforwardComp`, and the factorization hypothesis is absorbed
by an `eqToHom` on objects rather than by
`AlgebraicGeometry.Scheme.Modules.pushforwardCongr`: with the third morphism a variable, `subst`
reduces both of its lemmas to the case of the identity, where `eqToHom_refl` applies and the
action on sections is `rfl`.

## References

* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Section 02O7](https://stacks.math.columbia.edu/tag/02O7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

namespace Stacks.Cohomology.FormalFunctions

open Stacks.Algebraization

/-! ### Degree-zero derived global sections -/

/-- **The degree-zero right derived functor of global sections is global sections.**  Global
sections of sheaves of modules on a scheme preserves finite limits, being an evaluation, so the
canonical map from it to its zeroth right derived functor is an isomorphism. -/
public def moduleGlobalSectionsRightDerivedZeroIso (W : Scheme.{u}) :
    (AlgebraicGeometry.moduleGlobalSections W).rightDerived 0 ≅
      AlgebraicGeometry.moduleGlobalSections W :=
  (AlgebraicGeometry.moduleGlobalSections W).rightDerivedZeroIsoSelf

/-! ### Pushforwards of structure sheaves along a factorization -/

section Comparison

variable {Z : Scheme.{u}}

/-- A composite of morphisms of modules acts on sections as the composite of their actions.
Stated for variable modules, so that rewriting with it never unfolds the large objects of the
squares below. -/
private theorem comp_app_apply {W : Scheme.{u}} {M N K : W.Modules} (f : M ⟶ N) (g : N ⟶ K)
    (U : W.Opens) (x : Γ(M, U)) : (f ≫ g).app U x = g.app U (f.app U x) := rfl

/-- **The comparison of the direct images of structure sheaves along a factorization.**  For
`j ≫ w = v` with `j : V ⟶ W`, `w : W ⟶ Z`, the canonical morphism `w_* 𝒪_W ⟶ v_* 𝒪_V` of
`𝒪_Z`-modules, which on sections is restriction of functions along `j`. -/
public def pushforwardUnitComparison {W V : Scheme.{u}} (j : V ⟶ W) (w : W ⟶ Z) {v : V ⟶ Z}
    (hw : j ≫ w = v) :
    (Scheme.Modules.pushforward w).obj (Scheme.unitModule W) ⟶
      (Scheme.Modules.pushforward v).obj (Scheme.unitModule V) :=
  (Scheme.Modules.pushforward w).map (Scheme.Modules.unitToPushforwardUnit j) ≫
    (Scheme.Modules.pushforwardComp j w).hom.app (Scheme.unitModule V) ≫
      eqToHom (congrArg
        (fun f : V ⟶ Z => (Scheme.Modules.pushforward f).obj (Scheme.unitModule V)) hw)

/-- On global sections the comparison is restriction of functions along `j`. -/
public theorem pushforwardUnitComparison_app_top {W V : Scheme.{u}} (j : V ⟶ W) (w : W ⟶ Z)
    {v : V ⟶ Z} (hw : j ≫ w = v)
    (x : Γ((Scheme.Modules.pushforward w).obj (Scheme.unitModule W), (⊤ : Z.Opens))) :
    (pushforwardUnitComparison j w hw).app ⊤ x = j.appTop x := by
  subst hw
  rfl

/-- **The morphisms `𝒪_Z ⟶ v_* 𝒪_V` are compatible with the comparison**: the one for `w`
followed by the comparison along `j ≫ w = v` is the one for `v`. -/
public theorem unitToPushforwardUnit_comp_pushforwardUnitComparison {W V : Scheme.{u}}
    (j : V ⟶ W) (w : W ⟶ Z) {v : V ⟶ Z} (hw : j ≫ w = v) :
    Scheme.Modules.unitToPushforwardUnit w ≫ pushforwardUnitComparison j w hw =
      Scheme.Modules.unitToPushforwardUnit v := by
  subst hw
  rw [pushforwardUnitComparison, eqToHom_refl, Category.comp_id, ← Category.assoc]
  exact Scheme.Modules.unitToPushforwardUnit_comp j w

end Comparison

/-! ### The quotient by a power of an ideal sheaf and its closed subscheme -/

section Subscheme

variable {Z : Scheme.{u}} (J : Z.IdealSheafData)

/-- **The quotient `𝒪_Z / 𝓘 ⁿ 𝒪_Z` is the structure sheaf of the closed subscheme of `𝓘 ⁿ`.**
This is [Stacks, Tag 0EL1] at the closed immersion `(J ^ n).subschemeι`, whose ideal sheaf is
`J ^ n`, composed with the identification of the restriction of `𝒪_Z` to that subscheme with the
structure sheaf of the subscheme. -/
public def idealPowerQuotientSubschemeIso (n : ℕ) :
    idealPowerQuotient J n (Scheme.unitModule Z) ≅
      (Scheme.Modules.pushforward (J ^ n).subschemeι).obj
        (Scheme.unitModule (J ^ n).subscheme) :=
  idealQuotientPushforwardIso J n (Scheme.unitModule Z) (J ^ n).subschemeι
      (Scheme.IdealSheafData.ker_subschemeι _) ≪≫
    (Scheme.Modules.pushforward (J ^ n).subschemeι).mapIso
      (Scheme.Modules.pullbackUnitIso _)

/-- **The identification is compatible with the quotient projection**, at sheaf level: the
projection `𝒪_Z ⟶ 𝒪_Z / 𝓘 ⁿ 𝒪_Z` followed by the identification is the canonical morphism
`𝒪_Z ⟶ (ι_n)_* 𝒪_{(𝓘 ^ n).subscheme}`. -/
public theorem cokernel_π_comp_idealPowerQuotientSubschemeIso_hom (n : ℕ) :
    cokernel.π (C := Z.Modules) (idealPowerMultiple J n (Scheme.unitModule Z)).ι ≫
        (idealPowerQuotientSubschemeIso J n).hom =
      Scheme.Modules.unitToPushforwardUnit (J ^ n).subschemeι := by
  rw [idealPowerQuotientSubschemeIso, Iso.trans_hom, Functor.mapIso_hom, ← Category.assoc,
    idealQuotientPushforwardIso_hom, idealQuotientPushforwardMap_π]
  exact Scheme.Modules.pullbackUnitIso_homEquiv (J ^ n).subschemeι

/-- The closed immersion `(J ^ n).subscheme ⟶ (J ^ m).subscheme` of `n ≤ m`, induced by the
inclusion `J ^ m ≤ J ^ n` of ideal sheaves. -/
public abbrev idealPowerSubschemeInclusion {n m : ℕ} (h : n ≤ m) :
    (J ^ n).subscheme ⟶ (J ^ m).subscheme :=
  Scheme.IdealSheafData.inclusion (Scheme.IdealSheafData.pow_le_pow_of_le J h)

/-- Restriction of functions along the closed immersion `(J ^ n).subscheme ⟶ (J ^ m).subscheme`
of `n ≤ m`, as a morphism `(ι_m)_* 𝒪_{(𝓘 ^ m).subscheme} ⟶ (ι_n)_* 𝒪_{(𝓘 ^ n).subscheme}` of
`𝒪_Z`-modules. -/
public def idealPowerQuotientSubschemeDrop {n m : ℕ} (h : n ≤ m) :
    (Scheme.Modules.pushforward (J ^ m).subschemeι).obj
        (Scheme.unitModule (J ^ m).subscheme) ⟶
      (Scheme.Modules.pushforward (J ^ n).subschemeι).obj
        (Scheme.unitModule (J ^ n).subscheme) :=
  pushforwardUnitComparison (idealPowerSubschemeInclusion J h) (J ^ m).subschemeι
    (Scheme.IdealSheafData.inclusion_subschemeι _)

/-- On global sections the exponent-lowering map is restriction of functions along the closed
immersion `(J ^ n).subscheme ⟶ (J ^ m).subscheme`. -/
public theorem idealPowerQuotientSubschemeDrop_app_top {n m : ℕ} (h : n ≤ m)
    (y : Γ((Scheme.Modules.pushforward (J ^ m).subschemeι).obj
      (Scheme.unitModule (J ^ m).subscheme), (⊤ : Z.Opens))) :
    (idealPowerQuotientSubschemeDrop J h).app ⊤ y =
      (idealPowerSubschemeInclusion J h).appTop y :=
  pushforwardUnitComparison_app_top _ _ _ y

/-- **Naturality of the identification in `n`**, at sheaf level: for `n ≤ m`, lowering the
exponent of the quotient corresponds to restricting functions along the closed immersion
`(J ^ n).subscheme ⟶ (J ^ m).subscheme`.

Both composites are determined by their restriction along the quotient projection, which is an
epimorphism, and there both are the canonical morphism
`𝒪_Z ⟶ (ι_n)_* 𝒪_{(𝓘 ^ n).subscheme}`. -/
public theorem idealPowerQuotientSubschemeIso_naturality {n m : ℕ} (h : n ≤ m) :
    idealPowerQuotientDrop J h (Scheme.unitModule Z) ≫
        (idealPowerQuotientSubschemeIso J n).hom =
      (idealPowerQuotientSubschemeIso J m).hom ≫ idealPowerQuotientSubschemeDrop J h := by
  rw [← cancel_epi (cokernel.π (C := Z.Modules)
    (idealPowerMultiple J m (Scheme.unitModule Z)).ι), ← Category.assoc,
    idealPowerQuotientDrop_π, cokernel_π_comp_idealPowerQuotientSubschemeIso_hom,
    ← Category.assoc, cokernel_π_comp_idealPowerQuotientSubschemeIso_hom,
    idealPowerQuotientSubschemeDrop,
    unitToPushforwardUnit_comp_pushforwardUnitComparison]

/-! ### The identification on global sections -/

/-- **Global sections of `𝒪_Z / 𝓘 ⁿ 𝒪_Z` are the functions on the closed subscheme of `𝓘 ⁿ`**,
as `Γ(Z, ⊤)`-modules, where `Γ((J ^ n).subscheme, ⊤)` is a `Γ(Z, ⊤)`-module by restriction of
scalars along `(J ^ n).subschemeι`. -/
public def idealPowerQuotientSubschemeSectionsIso (n : ℕ) :
    letI : Module Γ(Z, ⊤) Γ((J ^ n).subscheme, ⊤) :=
      Module.compHom _ ((J ^ n).subschemeι.appTop).hom
    (AlgebraicGeometry.moduleGlobalSections Z).obj
        (idealPowerQuotient J n (Scheme.unitModule Z)) ≅
      ModuleCat.of Γ(Z, ⊤) Γ((J ^ n).subscheme, ⊤) :=
  (AlgebraicGeometry.moduleGlobalSections Z).mapIso (idealPowerQuotientSubschemeIso J n)

/-- The isomorphism of modules of global sections is global sections of the sheaf-level
isomorphism. -/
public theorem idealPowerQuotientSubschemeSectionsIso_hom (n : ℕ) :
    (idealPowerQuotientSubschemeSectionsIso J n).hom =
      (AlgebraicGeometry.moduleGlobalSections Z).map
        (idealPowerQuotientSubschemeIso J n).hom :=
  rfl

/-- The isomorphism of modules of global sections acts on a section as the sheaf-level
isomorphism does.  This is what makes the two squares below squares for
`Stacks.Cohomology.FormalFunctions.idealPowerQuotientSubschemeSectionsIso`. -/
public theorem idealPowerQuotientSubschemeSectionsIso_hom_apply (n : ℕ)
    (x : Γ(idealPowerQuotient J n (Scheme.unitModule Z), (⊤ : Z.Opens))) :
    (idealPowerQuotientSubschemeSectionsIso J n).hom x =
      (idealPowerQuotientSubschemeIso J n).hom.app ⊤ x :=
  rfl

/-- **Compatibility with the quotient projection**, on global sections: a global function on `Z`,
read in `Γ(Z, 𝒪_Z / 𝓘 ⁿ 𝒪_Z)` through the quotient projection and then through the
identification, is its restriction to the closed subscheme of `𝓘 ⁿ`. -/
public theorem idealPowerQuotientSubschemeSectionsIso_hom_app_top_π (n : ℕ) (x : Γ(Z, ⊤)) :
    (idealPowerQuotientSubschemeIso J n).hom.app ⊤
        ((cokernel.π (C := Z.Modules)
          (idealPowerMultiple J n (Scheme.unitModule Z)).ι).app ⊤ x) =
      (J ^ n).subschemeι.appTop x :=
  congrArg (fun φ : Scheme.unitModule Z ⟶ _ => φ.app ⊤ x)
    (cokernel_π_comp_idealPowerQuotientSubschemeIso_hom J n)

/-- **Naturality in `n`**, on global sections: for `n ≤ m`, the identification carries the
exponent-lowering map `Γ(Z, 𝒪_Z / 𝓘 ᵐ 𝒪_Z) ⟶ Γ(Z, 𝒪_Z / 𝓘 ⁿ 𝒪_Z)` to restriction of functions
along the closed immersion `(J ^ n).subscheme ⟶ (J ^ m).subscheme`. -/
public theorem idealPowerQuotientSubschemeSectionsIso_hom_app_top_drop {n m : ℕ} (h : n ≤ m)
    (x : Γ(idealPowerQuotient J m (Scheme.unitModule Z), (⊤ : Z.Opens))) :
    (idealPowerQuotientSubschemeIso J n).hom.app ⊤
        ((idealPowerQuotientDrop J h (Scheme.unitModule Z)).app ⊤ x) =
      (idealPowerSubschemeInclusion J h).appTop
        ((idealPowerQuotientSubschemeIso J m).hom.app ⊤ x) := by
  rw [← comp_app_apply, idealPowerQuotientSubschemeIso_naturality, comp_app_apply,
    idealPowerQuotientSubschemeDrop_app_top]

/-- **Naturality in `n`**, as a commuting square of `Γ(Z, ⊤)`-modules. -/
public theorem map_idealPowerQuotientDrop_comp_idealPowerQuotientSubschemeSectionsIso
    {n m : ℕ} (h : n ≤ m) :
    (AlgebraicGeometry.moduleGlobalSections Z).map
          (idealPowerQuotientDrop J h (Scheme.unitModule Z)) ≫
        (AlgebraicGeometry.moduleGlobalSections Z).map
          (idealPowerQuotientSubschemeIso J n).hom =
      (AlgebraicGeometry.moduleGlobalSections Z).map
          (idealPowerQuotientSubschemeIso J m).hom ≫
        (AlgebraicGeometry.moduleGlobalSections Z).map
          (idealPowerQuotientSubschemeDrop J h) := by
  rw [← Functor.map_comp, ← Functor.map_comp, idealPowerQuotientSubschemeIso_naturality]

end Subscheme

/-! ### The ideal sheaf of an ideal of an affine base -/

section BaseIdeal

variable (A : Type u) [CommRing A] {Z : Scheme.{u}} (g : Z ⟶ Spec (.of A)) (I : Ideal A)

/-- **Global sections of `𝒪_Z / I ⁿ 𝒪_Z` are the functions on the closed subscheme cut out by
`(I · 𝒪_Z) ⁿ`**, as `Γ(Z, ⊤)`-modules.  This is
`Stacks.Cohomology.FormalFunctions.idealPowerQuotientSubschemeSectionsIso` at the ideal sheaf
`I · 𝒪_Z` of an ideal of the affine base. -/
public def idealPowerQuotientSectionsIso (n : ℕ) :
    letI : Module Γ(Z, ⊤) Γ((baseIdealSheaf A I g ^ n).subscheme, ⊤) :=
      Module.compHom _ ((baseIdealSheaf A I g ^ n).subschemeι.appTop).hom
    (AlgebraicGeometry.moduleGlobalSections Z).obj
        (Stacks.Algebraization.idealPowerQuotient (baseIdealSheaf A I g) n
          (AlgebraicGeometry.Scheme.unitModule Z)) ≅
      ModuleCat.of Γ(Z, ⊤) Γ((baseIdealSheaf A I g ^ n).subscheme, ⊤) :=
  idealPowerQuotientSubschemeSectionsIso (baseIdealSheaf A I g) n

/-- **Compatibility with the quotient projection** for the ideal sheaf of an affine base. -/
public theorem idealPowerQuotientSectionsIso_hom_app_top_π (n : ℕ) (x : Γ(Z, ⊤)) :
    (idealPowerQuotientSubschemeIso (baseIdealSheaf A I g) n).hom.app ⊤
        ((cokernel.π (C := Z.Modules)
          (idealPowerMultiple (baseIdealSheaf A I g) n
            (Scheme.unitModule Z)).ι).app ⊤ x) =
      (baseIdealSheaf A I g ^ n).subschemeι.appTop x :=
  idealPowerQuotientSubschemeSectionsIso_hom_app_top_π _ n x

/-- **Naturality in `n`** for the ideal sheaf of an affine base. -/
public theorem idealPowerQuotientSectionsIso_hom_app_top_drop {n m : ℕ} (h : n ≤ m)
    (x : Γ(idealPowerQuotient (baseIdealSheaf A I g) m (Scheme.unitModule Z),
      (⊤ : Z.Opens))) :
    (idealPowerQuotientSubschemeIso (baseIdealSheaf A I g) n).hom.app ⊤
        ((idealPowerQuotientDrop (baseIdealSheaf A I g) h (Scheme.unitModule Z)).app ⊤ x) =
      (idealPowerSubschemeInclusion (baseIdealSheaf A I g) h).appTop
        ((idealPowerQuotientSubschemeIso (baseIdealSheaf A I g) m).hom.app ⊤ x) :=
  idealPowerQuotientSubschemeSectionsIso_hom_app_top_drop _ h x

/-- **The closed subscheme cut out by `(I · 𝒪_Z) ⁿ` is `Z ×_{Spec A} Spec (A / I ⁿ)`.**  The
`n`-th power of `I · 𝒪_Z` is the ideal sheaf of `I ^ n` by
`Stacks.Cohomology.FormalFunctions.baseIdealSheaf_pow`, and the subscheme cut out by the ideal
sheaf of an ideal of the base is the base change of its vanishing locus. -/
public def idealPowerSubschemeIsoPullback (n : ℕ) :
    (baseIdealSheaf A I g ^ n).subscheme ≅
      pullback g (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n)))) :=
  eqToIso (congrArg Scheme.IdealSheafData.subscheme
      (baseIdealSheaf_pow A I g n).symm) ≪≫
    Stacks.PuncturedSpectrumPicard.baseIdealSubschemeIsoPullback A (I ^ n) g

end BaseIdeal

end Stacks.Cohomology.FormalFunctions

end
