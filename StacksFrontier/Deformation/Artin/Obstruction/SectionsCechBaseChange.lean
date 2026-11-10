module

public import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.Degreewise
public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleBaseChangeComp
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatGlobalSections
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.TildeTensorSections
public import StacksFrontier.AlgebraicGeometry.SectionTensorFormula.AffineOpen
public import StacksFrontier.AlgebraicGeometry.TensorSheafSpellingIso.Basic
public import StacksFrontier.Deformation.Artin.Obstruction.SectionsPerfectComplex
public import StacksFrontier.Deformation.Artin.Obstruction.SectionsSheafSequence
public import StacksFrontier.Deformation.Artin.Obstruction.SectionsWComparison
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# The Čech model of `𝓕 ⊗_A M` is the base change of the Čech model of `𝓕`

Let `A` be a commutative ring, `f : X ⟶ Spec A` a morphism of schemes, `𝓖` a quasi-coherent
`𝒪_X`-module and `M` an `A`-module.  The functor `M ↦ f^* M̃ ⊗_{𝒪_X} 𝓖` of
[Stacks, Tag 07YH] — `Deformation.Artin.SectionsSheaf.tensorSheafFunctor` — produces a new
`𝒪_X`-module out of `M`, and this file identifies the `A`-linear alternating Čech model of that
module with the degreewise tensor product of `M` with the model of `𝓖`:

`Č_alt(𝒰, 𝓕 ⊗_A M)  ≅  M ⊗_A Č_alt(𝒰, 𝓕)`,

for a finite family `𝒰` of opens covering `X` all of whose finite intersections are affine.  No
flatness of `M` — and no flatness of `𝓖` — is needed: the alternating cochains in each degree are
a *finite product* of modules of sections, and a tensor product commutes with a finite product.

## Main definitions

* `Deformation.Artin.SectionsCechBaseChange.constMod`: the module `M ⊗ 𝒪_X = f^* M̃`.
* `Deformation.Artin.SectionsCechBaseChange.unitSection`: the section of `M ⊗ 𝒪_X` over an open
  attached to an element of `M`.
* `Deformation.Artin.SectionsCechBaseChange.compSection`: **the comparison on sections**, the
  product of that section with a section of `𝓖`.
* `Deformation.Artin.SectionsCechBaseChange.cochainComp` and
  `…SectionsCechBaseChange.alternatingCompTensor`: the comparison on Čech cochains and, out of
  the tensor product, on alternating Čech cochains.
* `Deformation.Artin.SectionsCechBaseChange.baseAlternatingCechTensorIso`: **the isomorphism of
  complexes.**

## Main results

* `…SectionsCechBaseChange.compSection_smul` and `…SectionsCechBaseChange.compSection_map`: the
  comparison on sections is balanced over `A` and compatible with restriction.  Those two
  properties are the whole content: commutation with the Čech differential
  (`…SectionsCechBaseChange.cochainComp_cechD`) and invariance of the alternating conditions
  (`…SectionsCechBaseChange.cochainComp_isAlternating`) are consequences of the second.
* `…SectionsCechBaseChange.isBaseChange_coeffSection`: **over an affine open the sections of
  `M ⊗ 𝒪_X` are the base change of `M`**, by [Stacks, Tag 01I9] in the form
  `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`.
* `…SectionsCechBaseChange.bijective_compSectionTensorHom`: **the comparison is bijective over an
  affine open** — the previous item together with the section formula of [Stacks, Tag 01I8] over
  an affine open.
* `…SectionsCechBaseChange.bijective_alternatingCompTensor`: **the comparison is bijective in
  each degree**, by `Stacks.Cech.ordLinearEquiv` and `TensorProduct.piRight`.
* `…SectionsCechBaseChange.isQuasicoherent_tensorSheafFunctor_obj`: `𝓕 ⊗_A M` is quasi-coherent,
  by [Stacks, Tag 01BG] and [Stacks, Tag 01CE].

## Implementation notes

**Three scalar rings, and why `Γ(Spec A, ⊤)` appears at all.**  The affine input
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` extends the scalars of `Γ(M̃, ⊤)` along
`f.appLE ⊤ W`, so it is a statement over `Γ(Spec A, ⊤)` rather than over `A`.  The crossing of
the ring isomorphism `A ≅ Γ(Spec A, ⊤)` is therefore done once, in
`bijective_compSectionTensorHom`, by `Stacks.SectionTensorFormula.bijective_of_tmulChange_eq`:
the two tensor products have the same pair of factors and the two canonical maps out of them
agree on pure tensors, so bijectivity of one gives bijectivity of the other.  The companion
crossing on the module side is `tildeTopSpec`, the identification `M ≅ Γ(M̃, ⊤)` of
`AlgebraicGeometry.TildeTensor.topEquiv` read over `Γ(Spec A, ⊤)`.

**Why `Algebra`, not `Module.compHom`.**  `ModuleCat.extendScalars` puts the `Module.compHom`
structure on the left factor, which is only definitionally the one coming from an `Algebra`
instance; comparing the two at a sheaf-section type diverges.  The comparison is crossed by
`AlgebraicGeometry.ModuleCat.isBaseChange_of_extendScalarsIso`, and everything downstream of
`isBaseChange_coeffSection` works with the `Algebra` structure, which is what
`TensorProduct.AlgebraTensorModule.cancelBaseChange` consumes.

**The linear order is chosen inside the proof.**  Neither the statement of
`bijective_alternatingCompTensor` nor that of `baseAlternatingCechTensorIso` mentions an order on
the index type, and `Stacks.Cech.ordLinearEquiv` needs one; as in
`Stacks.Cech.isBaseChange_alternatingCochainBaseChangeₗ` it is taken to be
`linearOrderOfSTO WellOrderingRel`.

**Flatness is not used.**  Flatness of the coefficient module enters the cohomology base-change
statements of `StacksFrontier/AlgebraicGeometry/FlatModuleCohomologyBaseChange/` only when homology
is commuted with the tensor product.  The identification of the *complexes* needs just
additivity, so this file carries no flatness hypothesis.

## References

* [Stacks Project, Tag 01FH](https://stacks.math.columbia.edu/tag/01FH)
* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 07YH](https://stacks.math.columbia.edu/tag/07YH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open TopologicalSpace Opposite
open Stacks.SectionTensorFormula Stacks.AlgebraicGeometry.SectionsBaseChange
open Stacks.AlgebraicGeometry.ModuleBaseChange
open scoped TensorProduct

universe u

namespace Deformation.Artin.SectionsCechBaseChange

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso Stacks.SheafInternalHom.isLocalization_sheafify
  Stacks.SheafInternalHom.monoidalCategory Stacks.SheafInternalHom.sheafifyMonoidal
  Stacks.SheafInternalHom.braidedCategory Stacks.SheafInternalHom.schemeMonoidalCategory

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- The quasi-coherent module on `Spec A` attached to an `A`-module. -/
abbrev tildeMod (M : ModuleCat.{u} A) : (Spec (CommRingCat.of A)).Modules :=
  AlgebraicGeometry.tilde.{u} (R := CommRingCat.of A) M

/-- `M ⊗ 𝒪_X`: the pullback along `f` of the quasi-coherent module attached to `M`. -/
abbrev constMod (M : ModuleCat.{u} A) : X.Modules :=
  (Scheme.Modules.pullback f).obj (tildeMod M)

/-- `M ⊗ 𝒪_X` is quasi-coherent. -/
instance isQuasicoherent_constMod (M : ModuleCat.{u} A) : (constMod f M).IsQuasicoherent :=
  inferInstanceAs ((Scheme.Modules.pullback f).obj (tildeMod M)).IsQuasicoherent

/-- `𝓖 ↦ (M ⊗ 𝒪_X) ⊗ 𝓖`: the target of the comparison, in the monoidal spelling. -/
abbrev tensorMod (M : ModuleCat.{u} A) (G : X.Modules) : X.Modules := constMod f M ⊗ G

variable (M : ModuleCat.{u} A)

/-- The global section of `M̃` attached to an element of `M`. -/
abbrev tildeTop (M : ModuleCat.{u} A) :=
  AlgebraicGeometry.TildeTensor.topEquiv (R := CommRingCat.of A) M

/-- The section of `M ⊗ 𝒪_X` over `W` attached to an element of `M`. -/
def unitSection (W : X.Opens) (m : M) : Γ(constMod f M, W) :=
  coeffSection f (tildeMod M) W (tildeTop M m)

/-- The section attached to `0 : M` is zero. -/
lemma unitSection_zero (W : X.Opens) : unitSection f M W 0 = 0 := by
  rw [unitSection, map_zero, coeffSection_zero]

/-- The section attached to an element of `M` is additive in that element. -/
lemma unitSection_add (W : X.Opens) (m m' : M) :
    unitSection f M W (m + m') = unitSection f M W m + unitSection f M W m' := by
  rw [unitSection, map_add, coeffSection_add]; rfl

/-- The section attached to `a • m` is the image of `a` in `Γ(X, W)` times the section attached
to `m`. -/
lemma unitSection_smul (W : X.Opens) (a : A) (m : M) :
    unitSection f M W (a • m) =
      (Stacks.Cech.baseRingHom f W).hom a • unitSection f M W m := by
  have h1 := (tildeTop M).map_smul a m
  rw [unitSection, unitSection, h1,
    Scheme.Modules.smul_Spec_def (R := CommRingCat.of A) (M := tildeMod M) (U := ⊤) a
      (tildeTop M m),
    show (⊤ : (Spec (CommRingCat.of A)).Opens).leTop.op = 𝟙 _ from Subsingleton.elim _ _,
    CategoryTheory.Functor.map_id, coeffSection_smul]
  rfl

/-- The section attached to an element of `M` is compatible with restriction. -/
lemma unitSection_res {V W : X.Opens} (h : V ≤ W) (m : M) :
    ((constMod f M).presheaf.map (homOfLE h).op).hom (unitSection f M W m) =
      unitSection f M V m :=
  coeffSection_res f (tildeMod M) h _

/-! ### The comparison on sections -/

variable (G : X.Modules)

/-- **The comparison on sections.**  The product of the section of `M ⊗ 𝒪_X` attached to
`m : M` with a section of `𝓖`. -/
def compSection (W : X.Opens) (m : M) (x : Γ(G, W)) : Γ(tensorMod f M G, W) :=
  tensorSection (constMod f M) G (unitSection f M W m) x

/-- The comparison on sections, as an additive map in the section of `𝓖`. -/
def compSectionHom (W : X.Opens) (m : M) : Γ(G, W) →+ Γ(tensorMod f M G, W) where
  toFun := compSection f M G W m
  map_zero' := tensorSection_zero_right _ _ _
  map_add' x y := tensorSection_add_right _ _ _ x y

/-- The additive map `compSectionHom f M G W m` sends `x` to `compSection f M G W m x`. -/
@[simp]
lemma compSectionHom_apply (W : X.Opens) (m : M) (x : Γ(G, W)) :
    compSectionHom f M G W m x = compSection f M G W m x := rfl

/-- The comparison on sections is additive in the element of `M`. -/
lemma compSection_add_left (W : X.Opens) (m m' : M) (x : Γ(G, W)) :
    compSection f M G W (m + m') x = compSection f M G W m x + compSection f M G W m' x := by
  rw [compSection, unitSection_add, tensorSection_add_left]; rfl

/-- The comparison on sections vanishes at `0 : M`. -/
lemma compSection_zero_left (W : X.Opens) (x : Γ(G, W)) :
    compSection f M G W 0 x = 0 := by
  rw [compSection, unitSection_zero, tensorSection_zero_left]

/-- **The comparison on sections is balanced over `A`.**  The base ring may be moved from the
module factor to the section factor. -/
lemma compSection_smul (W : X.Opens) (a : A) (m : M) (x : Γ(G, W)) :
    compSection f M G W (a • m) x =
      compSection f M G W m ((Stacks.Cech.baseRingHom f W).hom a • x) := by
  rw [compSection, compSection, unitSection_smul, tensorSection_smul_left,
    tensorSection_smul_right]

/-- **The comparison on sections is compatible with restriction.** -/
lemma compSection_map {V W : X.Opens} (i : V ⟶ W) (m : M) (x : Γ(G, W)) :
    ((tensorMod f M G).presheaf.map i.op).hom (compSection f M G W m x) =
      compSection f M G V m ((G.presheaf.map i.op).hom x) := by
  rw [compSection, compSection,
    show i = homOfLE i.le from Subsingleton.elim _ _]
  exact (map_tensorSection (constMod f M) G (homOfLE i.le) _ x).trans
    (congrArg (fun z => tensorSection (constMod f M) G z _) (unitSection_res f M i.le m))

/-- `compSection_map` in the spelling the Čech cochain groups use. -/
lemma compSection_restr {V W : X.Opens} (h : V ≤ W) (m : M) (x : Γ(G, W)) :
    CechCochains.restr (tensorMod f M G).presheaf h (compSection f M G W m x) =
      compSection f M G V m (CechCochains.restr G.presheaf h x) :=
  compSection_map f M G (homOfLE h) m x

/-! ### The comparison on Čech cochains -/

variable {I : Type u} (U : I → X.Opens)

/-- `compSection_map` against the permutation identification of the Čech cochain groups. -/
lemma compSection_permIso {p : ℕ} (i : Fin (p + 1) → I) (σ : Equiv.Perm (Fin (p + 1))) (m : M)
    (x : Γ(G, CechCochains.inter U i)) :
    CechCochains.permIso U (tensorMod f M G).presheaf i σ
        (compSection f M G (CechCochains.inter U i) m x) =
      compSection f M G (CechCochains.inter U (i ∘ σ)) m
        (CechCochains.permIso U G.presheaf i σ x) :=
  compSection_map f M G (eqToHom (by rw [CechCochains.inter_comp_perm U i σ])) m x

/-- **The comparison on Čech cochains**: apply the comparison on sections in each tuple. -/
def cochainComp (p : ℕ) (m : M) (s : CechCochains.Cochain U G.presheaf p) :
    CechCochains.Cochain U (tensorMod f M G).presheaf p :=
  fun i ↦ compSection f M G (CechCochains.inter U i) m (s i)

/-- The value of `cochainComp` at a tuple is the comparison on sections over the corresponding
intersection. -/
lemma cochainComp_apply (p : ℕ) (m : M) (s : CechCochains.Cochain U G.presheaf p)
    (i : Fin (p + 1) → I) :
    cochainComp f M G U p m s i = compSection f M G (CechCochains.inter U i) m (s i) := rfl

/-- The comparison on Čech cochains is additive in the cochain. -/
lemma cochainComp_add_right (p : ℕ) (m : M) (s t : CechCochains.Cochain U G.presheaf p) :
    cochainComp f M G U p m (s + t) =
      cochainComp f M G U p m s + cochainComp f M G U p m t := by
  funext i
  exact tensorSection_add_right _ _ _ (s i) (t i)

/-- The comparison on Čech cochains vanishes on the zero cochain. -/
lemma cochainComp_zero_right (p : ℕ) (m : M) :
    cochainComp f M G U p m 0 = 0 := by
  funext i
  exact tensorSection_zero_right _ _ _

/-- The comparison on Čech cochains is additive in the element of `M`. -/
lemma cochainComp_add_left (p : ℕ) (m m' : M) (s : CechCochains.Cochain U G.presheaf p) :
    cochainComp f M G U p (m + m') s =
      cochainComp f M G U p m s + cochainComp f M G U p m' s := by
  funext i
  exact compSection_add_left f M G _ m m' (s i)

/-- The comparison on Čech cochains vanishes at `0 : M`. -/
lemma cochainComp_zero_left (p : ℕ) (s : CechCochains.Cochain U G.presheaf p) :
    cochainComp f M G U p 0 s = 0 := by
  funext i
  exact compSection_zero_left f M G _ (s i)

/-- **The comparison on Čech cochains is balanced over `A`.** -/
lemma cochainComp_smul (p : ℕ) (a : A) (m : M) (s : CechCochains.Cochain U G.presheaf p) :
    letI := Stacks.Cech.cochainModule f U G p
    cochainComp f M G U p (a • m) s = cochainComp f M G U p m (a • s) := by
  let := Stacks.Cech.cochainModule f U G p
  funext i
  rw [cochainComp_apply, cochainComp_apply, Stacks.Cech.cochain_smul_apply,
    compSection_smul]

/-- **The comparison on Čech cochains is a morphism of complexes.** -/
lemma cochainComp_cechD (p : ℕ) (m : M) (s : CechCochains.Cochain U G.presheaf p) :
    CechCochains.cechD U (tensorMod f M G).presheaf p (cochainComp f M G U p m s) =
      cochainComp f M G U (p + 1) m (CechCochains.cechD U G.presheaf p s) := by
  funext i
  change ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
      CechCochains.restr (tensorMod f M G).presheaf (CechCochains.inter_le_omit U i j)
        (cochainComp f M G U p m s (i ∘ j.succAbove)) =
    compSection f M G (CechCochains.inter U i) m
      (∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        CechCochains.restr G.presheaf (CechCochains.inter_le_omit U i j)
          (s (i ∘ j.succAbove)))
  rw [← compSectionHom_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [AddMonoidHom.map_zsmul, compSectionHom_apply, cochainComp_apply,
    compSection_restr f M G (CechCochains.inter_le_omit U i j) m (s (i ∘ j.succAbove))]

/-- **The comparison on Čech cochains carries alternating cochains to alternating cochains.** -/
lemma cochainComp_isAlternating (p : ℕ) (m : M) (s : CechCochains.Cochain U G.presheaf p)
    (hs : CechCochains.IsAlternating U G.presheaf s) :
    CechCochains.IsAlternating U (tensorMod f M G).presheaf (cochainComp f M G U p m s) := by
  refine ⟨fun i hi ↦ ?_, fun i a b hab ↦ ?_⟩
  · rw [cochainComp_apply, hs.1 i hi]
    exact tensorSection_zero_right _ _ _
  · rw [cochainComp_apply, cochainComp_apply, hs.2 i a b hab, ← compSectionHom_apply, map_neg,
      compSectionHom_apply, compSection_permIso f M G U i (Equiv.swap a b) m (s i)]

/-- The comparison on sections is linear over `Γ(X, W)` in the section of `𝓖`. -/
lemma compSection_smul_right (W : X.Opens) (r : Γ(X, W)) (m : M) (x : Γ(G, W)) :
    compSection f M G W m (r • x) = r • compSection f M G W m x :=
  tensorSection_smul_right _ _ r _ x

/-- The comparison on Čech cochains is `A`-linear in the cochain. -/
lemma cochainComp_smul_right (p : ℕ) (a : A) (m : M)
    (s : CechCochains.Cochain U G.presheaf p) :
    letI := Stacks.Cech.cochainModule f U G p
    letI := Stacks.Cech.cochainModule f U (tensorMod f M G) p
    cochainComp f M G U p m (a • s) = a • cochainComp f M G U p m s := by
  let := Stacks.Cech.cochainModule f U G p
  let := Stacks.Cech.cochainModule f U (tensorMod f M G) p
  funext i
  rw [cochainComp_apply, Stacks.Cech.cochain_smul_apply, Stacks.Cech.cochain_smul_apply,
    cochainComp_apply, compSection_smul_right]

/-! ### The comparison on alternating Čech cochains -/

open Stacks.Cech in
/-- The comparison on alternating Čech cochains attached to a fixed element of `M`, as a map
linear over the base ring. -/
def alternatingCompₗ (p : ℕ) (m : M) :
    letI := cochainModule f U G p
    letI := cochainModule f U (tensorMod f M G) p
    alternatingSubmodule f U G p →ₗ[A] alternatingSubmodule f U (tensorMod f M G) p :=
  letI := cochainModule f U G p
  letI := cochainModule f U (tensorMod f M G) p
  { toFun := fun s ↦
      ⟨cochainComp f M G U p m s.1, cochainComp_isAlternating f M G U p m s.1 s.2⟩
    map_add' := fun s t ↦ Subtype.ext (cochainComp_add_right f M G U p m s.1 t.1)
    map_smul' := fun a s ↦ Subtype.ext (cochainComp_smul_right f M G U p a m s.1) }

open Stacks.Cech in
/-- The underlying cochain of `alternatingCompₗ f M G U p m s` is `cochainComp f M G U p m s`. -/
@[simp]
lemma alternatingCompₗ_coe (p : ℕ) (m : M)
    (s : letI := cochainModule f U G p; alternatingSubmodule f U G p) :
    letI := cochainModule f U G p
    letI := cochainModule f U (tensorMod f M G) p
    (alternatingCompₗ f M G U p m s).1 = cochainComp f M G U p m s.1 := rfl

open Stacks.Cech in
/-- **The comparison on alternating Čech cochains, as an `A`-bilinear map in the element of `M`
and the cochain.** -/
def alternatingCompBil (p : ℕ) :
    letI := cochainModule f U G p
    letI := cochainModule f U (tensorMod f M G) p
    M →ₗ[A] alternatingSubmodule f U G p →ₗ[A] alternatingSubmodule f U (tensorMod f M G) p :=
  letI := cochainModule f U G p
  letI := cochainModule f U (tensorMod f M G) p
  { toFun := alternatingCompₗ f M G U p
    map_add' := fun m m' ↦ LinearMap.ext fun s ↦
      Subtype.ext (cochainComp_add_left f M G U p m m' s.1)
    map_smul' := fun a m ↦ LinearMap.ext fun s ↦
      Subtype.ext ((cochainComp_smul f M G U p a m s.1).trans
        (cochainComp_smul_right f M G U p a m s.1)) }

open Stacks.Cech in
/-- **The comparison on alternating Čech cochains out of the tensor product.** -/
def alternatingCompTensor (p : ℕ) :
    letI := cochainModule f U G p
    letI := cochainModule f U (tensorMod f M G) p
    TensorProduct A M (alternatingSubmodule f U G p) →ₗ[A]
      alternatingSubmodule f U (tensorMod f M G) p :=
  letI := cochainModule f U G p
  letI := cochainModule f U (tensorMod f M G) p
  TensorProduct.lift (alternatingCompBil f M G U p)

open Stacks.Cech in
/-- On a pure tensor `m ⊗ₜ s`, the underlying cochain of `alternatingCompTensor` is
`cochainComp f M G U p m s`. -/
@[simp]
lemma alternatingCompTensor_tmul (p : ℕ) (m : M)
    (s : letI := cochainModule f U G p; alternatingSubmodule f U G p) :
    letI := cochainModule f U G p
    letI := cochainModule f U (tensorMod f M G) p
    (alternatingCompTensor f M G U p (m ⊗ₜ[A] s)).1 = cochainComp f M G U p m s.1 := rfl

/-! ### Bijectivity over an affine open -/

section Affine

variable (W : X.Opens)

/-- The `Γ(S, ⊤)`-algebra structure on `Γ(X, W)` used by the base-change comparison. -/
@[instance_reducible]
def openAlgebra : Algebra Γ(Spec (CommRingCat.of A), ⊤) Γ(X, W) :=
  (f.appLE ⊤ W (le_preimage_top f W)).hom.toAlgebra

/-- `M` as a module over the global functions of the base, through `Γ(Spec A, ⊤) ≅ A`. -/
@[instance_reducible]
def specModule : Module Γ(Spec (CommRingCat.of A), ⊤) M :=
  Module.compHom _ (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom

/-- `tildeTop` as a map linear over the global functions of the base. -/
def tildeTopSpecMap :
    letI := specModule M
    M →ₗ[Γ(Spec (CommRingCat.of A), ⊤)] Γ(tildeMod M, ⊤) :=
  letI := specModule M
  { toFun := tildeTop M
    map_add' := fun x y ↦ map_add (tildeTop M) x y
    map_smul' := fun b m ↦ by
      have h1 := (tildeTop M).map_smul ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom b) m
      refine h1.trans ?_
      rw [Scheme.Modules.smul_Spec_def (R := CommRingCat.of A) (M := tildeMod M) (U := ⊤),
        show (⊤ : (Spec (CommRingCat.of A)).Opens).leTop.op = 𝟙 _ from Subsingleton.elim _ _,
        CategoryTheory.Functor.map_id]
      exact congrArg (fun r ↦ r • tildeTop M m)
        (congrArg
          (fun φ : Γ(Spec (CommRingCat.of A), ⊤) ⟶ Γ(Spec (CommRingCat.of A), ⊤) ↦ φ.hom b)
          (Scheme.ΓSpecIso (CommRingCat.of A)).hom_inv_id) }

/-- `tildeTop` as an equivalence linear over the global functions of the base. -/
def tildeTopSpec :
    letI := specModule M
    M ≃ₗ[Γ(Spec (CommRingCat.of A), ⊤)] Γ(tildeMod M, ⊤) :=
  letI := specModule M
  LinearEquiv.ofBijective (tildeTopSpecMap M) (tildeTop M).bijective

/-- `tildeTopSpec M` agrees with `tildeTop M`. -/
@[simp]
lemma tildeTopSpec_apply (m : M) :
    letI := specModule M
    tildeTopSpec M m = tildeTop M m := rfl

example : (Scheme.ΓSpecIso (CommRingCat.of A)).inv =
    AlgebraicGeometry.toSpecΓ (CommRingCat.of A) := rfl

/-- The base ring acts on sections through the global functions of the base. -/
lemma baseRingHom_spec (b : Γ(Spec (CommRingCat.of A), ⊤)) (V : X.Opens) :
    (Stacks.Cech.baseRingHom f V).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom b) =
      (f.appLE ⊤ V (le_preimage_top f V)).hom b := by
  have h0 : ∀ x : A,
      (Stacks.Cech.baseRingHom f V).hom x =
        (f.appLE ⊤ V (le_preimage_top f V)).hom
          ((AlgebraicGeometry.toSpecΓ (CommRingCat.of A)).hom x) := fun _ ↦ rfl
  have h1 : (AlgebraicGeometry.toSpecΓ (CommRingCat.of A)).hom
      ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom b) = b :=
    congrArg (fun φ : Γ(Spec (CommRingCat.of A), ⊤) ⟶ Γ(Spec (CommRingCat.of A), ⊤) ↦ φ.hom b)
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom_inv_id
  rw [h0, h1]

/-- The actions of `Γ(Spec A, ⊤)` and `Γ(X, V)` on `Γ(N, V)` form a scalar tower. -/
theorem isScalarTower_base (N : X.Modules) (V : X.Opens) :
    letI := openAlgebra f V
    letI := baseModule f N V
    IsScalarTower Γ(Spec (CommRingCat.of A), ⊤) Γ(X, V) Γ(N, V) :=
  let := openAlgebra f V
  let := baseModule f N V
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- `coeffSection` as a map linear over the global functions of the base. -/
def coeffSectionₗ :
    letI := baseModule f (constMod f M) W
    Γ(tildeMod M, ⊤) →ₗ[Γ(Spec (CommRingCat.of A), ⊤)] Γ(constMod f M, W) :=
  letI := baseModule f (constMod f M) W
  { toFun := coeffSection f (tildeMod M) W
    map_add' := coeffSection_add f (tildeMod M) W
    map_smul' := coeffSection_smul f (tildeMod M) W }

/-- **The sections of `M ⊗ 𝒪_X` over an affine open are the base change of `M`.** -/
theorem isBaseChange_coeffSection (hW : IsAffineOpen W) :
    letI := openAlgebra f W
    letI := baseModule f (constMod f M) W
    letI := isScalarTower_base f (constMod f M) W
    IsBaseChange Γ(X, W) (coeffSectionₗ f M W) :=
  let := openAlgebra f W
  let := baseModule f (constMod f M) W
  let := isScalarTower_base f (constMod f M) W
  AlgebraicGeometry.ModuleCat.isBaseChange_of_extendScalarsIso
    (f.appLE ⊤ W (le_preimage_top f W)).hom rfl
    (AlgebraicGeometry.affinePullbackSectionsBaseChangeIso f (tildeMod M)
      (isAffineOpen_top (Spec (CommRingCat.of A))) hW (le_preimage_top f W))
    (coeffSectionₗ f M W)
    (fun n ↦ AlgebraicGeometry.affinePullbackSectionsBaseChangeIso_one_tmul f (tildeMod M)
      (isAffineOpen_top (Spec (CommRingCat.of A))) hW (le_preimage_top f W) n)

/-- **The comparison over an affine open, over the global functions of the base.** -/
def compSectionSpecHom :
    letI := specModule M
    letI := baseModule f G W
    TensorProduct Γ(Spec (CommRingCat.of A), ⊤) M Γ(G, W) →+ Γ(tensorMod f M G, W) :=
  letI := specModule M
  letI := baseModule f G W
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun m ↦ compSectionHom f M G W m)
      (fun m m' ↦ AddMonoidHom.ext fun x ↦ compSection_add_left f M G W m m' x))
    (fun b m x ↦ by
      change compSection f M G W ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom b • m) x = _
      rw [compSection_smul, baseRingHom_spec]
      rfl)

/-- `compSectionSpecHom` sends `m ⊗ₜ x` to `compSection f M G W m x`. -/
lemma compSectionSpecHom_tmul (m : M) (x : Γ(G, W)) :
    letI := specModule M
    letI := baseModule f G W
    compSectionSpecHom f M G W (m ⊗ₜ[Γ(Spec (CommRingCat.of A), ⊤)] x) =
      compSection f M G W m x := rfl

/-- **The comparison over an affine open is bijective**, over the global functions of the
base. -/
theorem bijective_compSectionSpecHom [G.IsQuasicoherent] (hW : IsAffineOpen W) :
    letI := specModule M
    letI := baseModule f G W
    Function.Bijective (compSectionSpecHom f M G W) := by
  let := openAlgebra f W
  let := specModule M
  let := baseModule f G W
  let := baseModule f (constMod f M) W
  let := isScalarTower_base f G W
  let := isScalarTower_base f (constMod f M) W
  have hbc := isBaseChange_coeffSection f M W hW
  set e1 := TensorProduct.congr (tildeTopSpec M)
    (LinearEquiv.refl Γ(Spec (CommRingCat.of A), ⊤) Γ(G, W)) with he1
  set e2 := TensorProduct.comm Γ(Spec (CommRingCat.of A), ⊤) Γ(tildeMod M, ⊤) Γ(G, W) with he2
  set e3 := (TensorProduct.AlgebraTensorModule.cancelBaseChange
    Γ(Spec (CommRingCat.of A), ⊤) Γ(X, W) Γ(X, W) Γ(G, W) Γ(tildeMod M, ⊤)).symm with he3
  set e4 := TensorProduct.congr (LinearEquiv.refl Γ(X, W) Γ(G, W)) hbc.equiv with he4
  set e5 := TensorProduct.comm Γ(X, W) Γ(G, W) Γ(constMod f M, W) with he5
  set e6 := tensorSectionEquiv (constMod f M) G hW with he6
  have hcomp : ∀ z, compSectionSpecHom f M G W z = e6 (e5 (e4 (e3 (e2 (e1 z))))) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul m x =>
        simp only [compSectionSpecHom_tmul, he1, he2, he3, he4, he5, he6,
          TensorProduct.congr_tmul, LinearEquiv.refl_apply, TensorProduct.comm_tmul,
          TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
          IsBaseChange.equiv_tmul, one_smul, tensorSectionEquiv_tmul]
        rfl
    | add a b ha hb => rw [map_add, ha, hb]; simp
  rw [show ⇑(compSectionSpecHom f M G W) = fun z ↦ e6 (e5 (e4 (e3 (e2 (e1 z))))) from
    funext hcomp]
  exact e6.bijective.comp (e5.bijective.comp (e4.bijective.comp
    (e3.bijective.comp (e2.bijective.comp e1.bijective))))

/-- **The comparison over an affine open, out of the tensor product over the base ring.** -/
def compSectionTensorHom :
    letI := Stacks.Cech.sectionsModule f G W
    TensorProduct A M Γ(G, W) →+ Γ(tensorMod f M G, W) :=
  letI := Stacks.Cech.sectionsModule f G W
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun m ↦ compSectionHom f M G W m)
      (fun m m' ↦ AddMonoidHom.ext fun x ↦ compSection_add_left f M G W m m' x))
    (fun a m x ↦ compSection_smul f M G W a m x)

/-- **The comparison over an affine open is bijective.**  This is the affine case of the
section formula of [Stacks, Tag 01I8] together with [Stacks, Tag 01I9]: the sections of
`M ⊗ 𝒪_X` over an affine open are the base change of `M`. -/
theorem bijective_compSectionTensorHom [G.IsQuasicoherent] (hW : IsAffineOpen W) :
    letI := Stacks.Cech.sectionsModule f G W
    Function.Bijective (compSectionTensorHom f M G W) := by
  let := specModule M
  let := baseModule f G W
  let := Stacks.Cech.sectionsModule f G W
  refine bijective_of_tmulChange_eq (compSectionTensorHom f M G W) (compSectionSpecHom f M G W)
    ?_ (fun _ _ ↦ rfl) (bijective_compSectionSpecHom f M G W hW)
  intro b m x
  have h1 : (b • m : M) = ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom b : A) • m := rfl
  have h2 : (b • x : Γ(G, W)) = ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom b : A) • x :=
    (congrArg (fun r : Γ(X, W) ↦ r • x) (baseRingHom_spec f b W)).symm
  rw [h1, h2, TensorProduct.smul_tmul]

end Affine

/-! ### Bijectivity in each degree -/

section Degreewise

open Stacks.Cech in
/-- **The comparison is bijective in each degree.**  Through `Stacks.Cech.ordLinearEquiv` the
alternating cochains are a finite product of modules of sections over the intersections of the
cover, which are affine; so this is the affine case
`bijective_compSectionTensorHom` together with the commutation of a tensor
product with a finite product. -/
theorem bijective_alternatingCompTensor [G.IsQuasicoherent] [Finite I]
    (haff : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, U (s k))) (p : ℕ) :
    letI := cochainModule f U G p
    letI := cochainModule f U (tensorMod f M G) p
    Function.Bijective (alternatingCompTensor f M G U p) := by
  let := cochainModule f U G p
  let := cochainModule f U (tensorMod f M G) p
  let : DecidableRel (WellOrderingRel : I → I → Prop) := Classical.decRel _
  let : LinearOrder I := linearOrderOfSTO WellOrderingRel
  let : ∀ j : CechCochains.OrdIndex (I := I) p,
      Module A Γ(G, CechCochains.inter U j.1) := fun _ ↦ sectionsModule f G _
  let : ∀ j : CechCochains.OrdIndex (I := I) p,
      Module A Γ(tensorMod f M G, CechCochains.inter U j.1) := fun _ ↦ sectionsModule f _ _
  let := ordCochainModule f U G p
  let := ordCochainModule f U (tensorMod f M G) p
  let : Fintype (CechCochains.OrdIndex (I := I) p) := Fintype.ofFinite _
  let : DecidableEq (CechCochains.OrdIndex (I := I) p) := Classical.decEq _
  set e1 : TensorProduct A M (alternatingSubmodule f U G p) ≃ₗ[A]
      TensorProduct A M
        (∀ j : CechCochains.OrdIndex (I := I) p, Γ(G, CechCochains.inter U j.1)) :=
    TensorProduct.congr (LinearEquiv.refl A M) (ordLinearEquiv f U G p) with he1
  set e2 := TensorProduct.piRight A A M
    (fun j : CechCochains.OrdIndex (I := I) p ↦ Γ(G, CechCochains.inter U j.1)) with he2
  set e3 : (∀ j : CechCochains.OrdIndex (I := I) p,
        TensorProduct A M Γ(G, CechCochains.inter U j.1)) ≃+
      (∀ j : CechCochains.OrdIndex (I := I) p,
        Γ(tensorMod f M G, CechCochains.inter U j.1)) :=
    AddEquiv.piCongrRight (fun j ↦ AddEquiv.ofBijective
      (compSectionTensorHom f M G (CechCochains.inter U j.1))
      (bijective_compSectionTensorHom f M G (CechCochains.inter U j.1)
        (haff p j.1))) with he3
  set e4 : alternatingSubmodule f U (tensorMod f M G) p ≃ₗ[A]
      (∀ j : CechCochains.OrdIndex (I := I) p,
        Γ(tensorMod f M G, CechCochains.inter U j.1)) :=
    ordLinearEquiv f U (tensorMod f M G) p with he4
  have hcomp : ∀ z, e4 (alternatingCompTensor f M G U p z) = e3 (e2 (e1 z)) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul m s => rfl
    | add a b ha hb => simp only [map_add]; rw [ha, hb]
  refine (e4.bijective.of_comp_iff' _).mp ?_
  rw [show e4 ∘ alternatingCompTensor f M G U p = fun z ↦ e3 (e2 (e1 z)) from funext hcomp]
  exact e3.bijective.comp (e2.bijective.comp e1.bijective)

end Degreewise

/-! ### The isomorphism of complexes -/

section Complex

variable [G.IsQuasicoherent] [Finite I]
  (haff : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, U (s k)))

open Stacks.Cech in
/-- The degreewise comparison, as an isomorphism of `A`-modules. -/
def alternatingCompObjIso (p : ℕ) :
    ((curriedTensor (ModuleCat.{u} A)).obj M).obj (alternatingCechModuleObj f U G p) ≅
      alternatingCechModuleObj f U (tensorMod f M G) p :=
  letI := cochainModule f U G p
  letI := cochainModule f U (tensorMod f M G) p
  (LinearEquiv.ofBijective (alternatingCompTensor f M G U p)
    (bijective_alternatingCompTensor f M G U haff p)).toModuleIso

open Stacks.Cech in
/-- **The isomorphism of `ℕ`-indexed alternating Čech complexes.** -/
def alternatingCompComplexIso :
    (((curriedTensor (ModuleCat.{u} A)).obj M).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (alternatingCechModuleComplex f U G) ≅
      alternatingCechModuleComplex f U (tensorMod f M G) := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun p ↦ alternatingCompObjIso f M G U haff p) ?_
  rintro p q (rfl : p + 1 = q)
  rw [Functor.mapHomologicalComplex_obj_d, alternatingCechModuleComplex_d,
    alternatingCechModuleComplex_d]
  let := cochainModule f U G p
  let := cochainModule f U G (p + 1)
  let := cochainModule f U (tensorMod f M G) p
  let := cochainModule f U (tensorMod f M G) (p + 1)
  refine ModuleCat.hom_ext (TensorProduct.ext' fun m s ↦ ?_)
  exact Subtype.ext (cochainComp_cechD f M G U p m s.1)

/-- **The target of the comparison is the base-changed sheaf of Stacks 07YH.** -/
def tensorModIso :
    tensorMod f M G ≅ (Deformation.Artin.SectionsSheaf.tensorSheafFunctor f G).obj M :=
  Stacks.TensorSheafSpellingIso.monoidalTensorIso X (constMod f M) G

variable (hU : (⊤ : X.Opens) = ⨆ i, U i)

open Stacks.AlgebraicGeometry.ProperFlatGlobalSections
open Deformation.Artin.SectionsSheaf (tensorSheafFunctor)
open Deformation.Artin.SectionsPerfectComplex (tensorComplex)

/-- **The base-changed Čech model is the base change of the Čech model.** -/
def baseAlternatingCechTensorIso :
    baseAlternatingCechComplex f U hU ((tensorSheafFunctor f G).obj M) ≅
      (tensorComplex M).obj (baseAlternatingCechComplex f U hU G) :=
  baseAlternatingCechComplexIsoExtend f U hU ((tensorSheafFunctor f G).obj M) ≪≫
    (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} A)).mapIso
      (Stacks.Cech.alternatingCechModuleComplexMapIso f U (tensorModIso f M G)).symm ≪≫
    (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} A)).mapIso
      (alternatingCompComplexIso f M G U haff).symm ≪≫
    Stacks.DerivedIndexing.mapExtendIso ((curriedTensor (ModuleCat.{u} A)).obj M)
      ComplexShape.embeddingUpNat (Stacks.Cech.alternatingCechModuleComplex f U G) ≪≫
    (tensorComplex M).mapIso (baseAlternatingCechComplexIsoExtend f U hU G).symm

end Complex


/-! ### Quasi-coherence of the base-changed module -/

/-- **`𝓖 ⊗_A M` is quasi-coherent** for a base spelled `Spec (.of A)` with `A` a type.  This is
`Deformation.Artin.SectionsSheaf.isQuasicoherent_tensorSheafFunctor_obj`, which instance search
does not find at this spelling because the coefficient ring has to be read off the type `A` of
the module rather than from a `CommRingCat`. -/
instance isQuasicoherent_tensorSheafFunctor_obj_specOf (M : ModuleCat.{u} A) (G : X.Modules)
    [G.IsQuasicoherent] :
    ((Deformation.Artin.SectionsSheaf.tensorSheafFunctor f G).obj M).IsQuasicoherent :=
  Deformation.Artin.SectionsSheaf.isQuasicoherent_tensorSheafFunctor_obj f G M

end Deformation.Artin.SectionsCechBaseChange

end
