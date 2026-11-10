module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.AlternatingComplex
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The alternating Čech complex of a sheaf of modules, linearly over an affine base

Let `A` be a commutative ring, let `f : X ⟶ Spec A` be a scheme over the affine base, let
`F` be a sheaf of `𝒪_X`-modules and let `U : I → X.Opens` be a family of open subsets. Every
section of `F` over an open `W` is a module over `Γ(X, W)`, hence over `A` through the
structural map `A → Γ(X, ⊤) → Γ(X, W)`; the Čech cochains of `F` with respect to `U` are
therefore `A`-modules, the Čech differential is `A`-linear, and the alternating cochains form
an `A`-submodule. This file builds the resulting two complexes of `A`-modules and the
canonical comparison between them, and identifies them with the abelian-group-valued
complexes of Stacks 01FH after forgetting the module structures.

## Main definitions

* `Stacks.Cech.baseRingHom`: the structural ring map `A → Γ(X, W)` of a scheme over `Spec A`.
* `Stacks.Cech.sectionsModule`: the `A`-module structure on `Γ(F, W)` it induces.
* `Stacks.Cech.cochainModule`: the `A`-module structure on the degree-`p` Čech cochains.
* `Stacks.Cech.alternatingSubmodule`: the alternating cochains as an `A`-submodule.
* `Stacks.Cech.cechModuleComplex`: the usual Čech complex as a complex of `A`-modules.
* `Stacks.Cech.alternatingCechModuleComplex`: the alternating Čech complex as a complex of
  `A`-modules.
* `Stacks.Cech.alternatingCechModuleComplex_inclusion`: the `A`-linear
  alternating-to-usual Čech comparison.

## Main results

* `Stacks.Cech.cechModuleComplex_smul_eval`,
  `Stacks.Cech.alternatingCechModuleComplex_smul_eval` and
  `Stacks.Cech.cochain_smul_apply`: the scalar action on a Čech cochain is, in every tuple,
  the action on sections induced by the structural map to `Spec A` — not merely some linear
  structure on the underlying group. `Stacks.Cech.baseRingHom_eq_appLE` names that structural
  map as `Scheme.Hom.appLE` of `f` composed with `AlgebraicGeometry.toSpecΓ`, so the two
  evaluation formulas mention no auxiliary definition of this file.
* `Stacks.Cech.cechModuleComplex_forget` and
  `Stacks.Cech.alternatingCechModuleComplex_forget`: forgetting the module structures
  recovers `Stacks.Cech.cechComplex` and `Stacks.Cech.alternatingCechComplex`.
* `Stacks.Cech.alternatingCechModuleComplex_inclusion_forget`: forgetting the `A`-linear
  comparison gives `Stacks.Cech.alternatingCechInclusion`, the inclusion of Stacks 01FH, and
  not merely some quasi-isomorphism.
* `Stacks.Cech.alternatingCechModuleComplex_bounded`: for a finite index type the alternating
  complex vanishes in every degree `≥ Fintype.card I`.

## Implementation notes

**The cochains are the ones of Stacks 01FH, carrying extra structure.** The degree-`p` term is
`ModuleCat.of A (CechCochains.Cochain U F.presheaf p)` and the alternating term is
`ModuleCat.of A (alternatingSubmodule f U F p)`, whose carrier is *the same type* as
`CechCochains.alternatingSubgroup U F.presheaf p` — `alternatingSubmodule` is built by adding
`smul_mem'` to that subgroup. Consequently the two `_forget` identifications are
`Iso.refl`-valued degreewise, so they cannot silently be the wrong map, and
`alternatingCechModuleComplex_inclusion_forget` is a statement about the actual subgroup
inclusion rather than about an abstract comparison. This is the reason the shape was chosen:
boundedness, flatness and the comparison with the Ab-valued theory are then all statements
about one and the same family of groups.

**The module structure is a `def`, not an instance.** `Module A Γ(F, W)` is obtained from the
canonical `Module Γ(X, W) Γ(F, W)` by `Module.compHom` along `baseRingHom f W`, which depends
on the morphism `f` and so cannot be found by instance search. `sectionsModule`,
`cochainModule` and `alternatingSubmodule` are therefore `def`s introduced by `letI` where
they are used, and every statement about the scalar action names `baseRingHom` explicitly.

**`baseRingHom` factors through a separate `globalRingHom`.** Writing the structural map as
one composite `toSpecΓ _ ≫ f.appTop ≫ X.presheaf.map _` makes `Category.assoc` fail silently
on it: `f.appTop` presents its codomain as `Γ(X, f ⁻¹ᵁ ⊤)`, which is only `rfl`-equal to the
`Γ(X, ⊤)` that the restriction map expects, and a composite mixing two spellings of its middle
object is not rewritten by `assoc`. Declaring `globalRingHom` with result type `Γ(X, ⊤)` pins
the spelling, after which `baseRingHom_map` is three rewrites.

**The index family, not a cover.** The construction uses nothing about `U` beyond its being an
indexed family of opens, so no covering hypothesis and no affineness is an argument here; a
client that needs them supplies them where it uses them. In particular, for an affine open
cover `T : X.AffineOpenCover` the complexes of Stacks 01XL are obtained by taking
`U := fun i ↦ (T.f i).opensRange`, and `Fintype T.I₀` supplies the `Fintype I` that
`alternatingCechModuleComplex_bounded` needs.

**No `@[stacks]` attribute.** Stacks 01FH already has its two carriers, the complex and its
canonical inclusion, in `StacksDraft.Ch20.Sec23.AlternatingCechComplex`; the declarations here
state the same two things with an `A`-module structure added, which is a refinement rather than
a different clause of the tag. Stacks 01XL is the computation of `Rf_*F` by this complex, which
is not proved here.

## References

* [Stacks Project, Tag 01FH](https://stacks.math.columbia.edu/tag/01FH)
* [Stacks Project, Tag 01FJ](https://stacks.math.columbia.edu/tag/01FJ)
* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

noncomputable section

namespace Stacks.Cech

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-! ### The `A`-module structure on sections -/

/-- The ring map `A → Γ(X, ⊤)` of a scheme over the affine base `Spec A`.

Declared with result type `Γ(X, ⊤)`: the codomain of `f.appTop` is spelled `Γ(X, f ⁻¹ᵁ ⊤)`,
and a composite that mixes the two spellings is invisible to `Category.assoc`. -/
def globalRingHom : CommRingCat.of A ⟶ Γ(X, ⊤) :=
  toSpecΓ (CommRingCat.of A) ≫ f.appTop

/-- The structural ring map `A → Γ(X, W)`: the map on global functions induced by `f`,
followed by restriction to `W`. -/
def baseRingHom (W : X.Opens) : CommRingCat.of A ⟶ Γ(X, W) :=
  globalRingHom f ≫ X.presheaf.map (homOfLE le_top).op

/-- The structural ring maps are compatible with restriction. -/
theorem baseRingHom_map {V W : X.Opens} (g : op V ⟶ op W) :
    baseRingHom f V ≫ X.presheaf.map g = baseRingHom f W := by
  simp only [baseRingHom, Category.assoc, ← Functor.map_comp]
  rfl

/-- The elementwise form of `Stacks.Cech.baseRingHom_map`. -/
theorem map_baseRingHom_apply {V W : X.Opens} (g : op V ⟶ op W) (a : A) :
    (X.presheaf.map g).hom ((baseRingHom f V).hom a) = (baseRingHom f W).hom a :=
  congrFun (congrArg (fun h : CommRingCat.of A ⟶ Γ(X, W) => h.hom.toFun)
    (baseRingHom_map f g)) a

/-- The structural ring map `A → Γ(X, W)` is the map on global functions of `Spec A` followed
by the restriction `f.appLE` to `W`.

This identifies the module structure used throughout this file as the one induced by the
morphism `f` to the affine base, and not merely as some linear structure: no freedom is left
in it once `f` is given. -/
theorem baseRingHom_eq_appLE (W : X.Opens) (h : W ≤ f ⁻¹ᵁ ⊤) :
    baseRingHom f W = toSpecΓ (CommRingCat.of A) ≫ f.appLE ⊤ W h :=
  rfl

/-- Sections of an `𝒪_X`-module over an open subset are a module over the base ring, through
the structural map of `f`. -/
@[instance_reducible]
def sectionsModule (F : X.Modules) (W : X.Opens) : Module A Γ(F, W) :=
  Module.compHom _ (baseRingHom f W).hom

variable {I : Type u} (U : I → X.Opens) (F : X.Modules)

/-! ### The `A`-module structure on Čech cochains -/

/-- Degree-`p` Čech cochains of `F` with respect to `U` form an `A`-module, tuplewise. -/
@[instance_reducible]
def cochainModule (p : ℕ) : Module A (CechCochains.Cochain U F.presheaf p) :=
  letI : ∀ i : Fin (p + 1) → I, Module A Γ(F, CechCochains.inter U i) :=
    fun _ => sectionsModule f F _
  inferInstanceAs (Module A (∀ i : Fin (p + 1) → I, Γ(F, CechCochains.inter U i)))

/-- The scalar action on a Čech cochain is, in every tuple, the action on sections induced by
the structural map to the affine base. -/
theorem cochain_smul_apply (p : ℕ) (a : A) (s : CechCochains.Cochain U F.presheaf p)
    (i : Fin (p + 1) → I) :
    letI := cochainModule f U F p
    (a • s) i = (baseRingHom f (CechCochains.inter U i)).hom a • s i :=
  rfl

/-- The identification of sections along a permutation of the index tuple is `A`-linear. -/
theorem permIso_smul (p : ℕ) (i : Fin (p + 1) → I) (σ : Equiv.Perm (Fin (p + 1))) (a : A)
    (x : Γ(F, CechCochains.inter U i)) :
    CechCochains.permIso U F.presheaf i σ ((baseRingHom f (CechCochains.inter U i)).hom a • x) =
      (baseRingHom f (CechCochains.inter U (i ∘ σ))).hom a •
        CechCochains.permIso U F.presheaf i σ x := by
  change (F.presheaf.map _).hom _ = _
  rw [Scheme.Modules.map_smul, map_baseRingHom_apply]
  rfl

/-- The Čech differential is `A`-linear. -/
theorem cechD_smul (p : ℕ) (a : A) (s : CechCochains.Cochain U F.presheaf p) :
    letI := cochainModule f U F p
    letI := cochainModule f U F (p + 1)
    CechCochains.cechD U F.presheaf p (a • s) = a • CechCochains.cechD U F.presheaf p s := by
  let := cochainModule f U F p
  let := cochainModule f U F (p + 1)
  funext i
  rw [cochain_smul_apply]
  change (∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        CechCochains.restr F.presheaf (CechCochains.inter_le_omit U i j)
          ((a • s) (i ∘ j.succAbove))) =
      _ • ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        CechCochains.restr F.presheaf (CechCochains.inter_le_omit U i j) (s (i ∘ j.succAbove))
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [cochain_smul_apply]
  change ((-1 : ℤ) ^ (j : ℕ)) • F.presheaf.map _ (_ • s (i ∘ j.succAbove)) = _
  rw [Scheme.Modules.map_smul, map_baseRingHom_apply]
  exact (smul_comm _ _ _).symm

/-- The Čech differential as an `A`-linear map. -/
def cechModuleD (p : ℕ) :
    letI := cochainModule f U F p
    letI := cochainModule f U F (p + 1)
    CechCochains.Cochain U F.presheaf p →ₗ[A] CechCochains.Cochain U F.presheaf (p + 1) :=
  letI := cochainModule f U F p
  letI := cochainModule f U F (p + 1)
  { toFun := CechCochains.cechD U F.presheaf p
    map_add' := map_add _
    map_smul' := cechD_smul f U F p }

/-- The alternating Čech cochains of Stacks 01FH form an `A`-submodule of all cochains.

Its carrier is the carrier of `CechCochains.alternatingSubgroup`, so the two coercions to types
agree. -/
def alternatingSubmodule (p : ℕ) :
    letI := cochainModule f U F p
    Submodule A (CechCochains.Cochain U F.presheaf p) :=
  letI := cochainModule f U F p
  { CechCochains.alternatingSubgroup U F.presheaf p with
    smul_mem' := fun a s hs => by
      refine ⟨fun i hi => by rw [cochain_smul_apply, hs.1 i hi, smul_zero], fun i b b' hbb' => ?_⟩
      rw [cochain_smul_apply, cochain_smul_apply, hs.2 i b b' hbb', permIso_smul, smul_neg] }

/-- The alternating Čech differential as an `A`-linear map. -/
def alternatingCechModuleD (p : ℕ) :
    letI := cochainModule f U F p
    letI := cochainModule f U F (p + 1)
    alternatingSubmodule f U F p →ₗ[A] alternatingSubmodule f U F (p + 1) :=
  letI := cochainModule f U F p
  letI := cochainModule f U F (p + 1)
  (cechModuleD f U F p).restrict
    (fun s hs => CechCochains.cechD_mem_alternating U F.presheaf p s hs)

/-! ### The two complexes of `A`-modules -/

/-- The degree-`p` term of the usual Čech complex of `A`-modules: all Čech cochains. -/
def cechModuleObj (p : ℕ) : ModuleCat.{u} A :=
  letI := cochainModule f U F p
  ModuleCat.of A (CechCochains.Cochain U F.presheaf p)

/-- The degree-`p` term of the alternating Čech complex of `A`-modules: the alternating Čech
cochains. -/
def alternatingCechModuleObj (p : ℕ) : ModuleCat.{u} A :=
  letI := cochainModule f U F p
  ModuleCat.of A (alternatingSubmodule f U F p)

/-- The Čech differential, as a morphism of `A`-modules. -/
def cechModuleDiff (p : ℕ) : cechModuleObj f U F p ⟶ cechModuleObj f U F (p + 1) :=
  letI := cochainModule f U F p
  letI := cochainModule f U F (p + 1)
  ModuleCat.ofHom (cechModuleD f U F p)

/-- The alternating Čech differential, as a morphism of `A`-modules. -/
def alternatingCechModuleDiff (p : ℕ) :
    alternatingCechModuleObj f U F p ⟶ alternatingCechModuleObj f U F (p + 1) :=
  letI := cochainModule f U F p
  letI := cochainModule f U F (p + 1)
  ModuleCat.ofHom (alternatingCechModuleD f U F p)

/-- The degreewise inclusion of the alternating cochains into all cochains, as a morphism of
`A`-modules. -/
def alternatingCechModuleSubtype (p : ℕ) :
    alternatingCechModuleObj f U F p ⟶ cechModuleObj f U F p :=
  letI := cochainModule f U F p
  ModuleCat.ofHom (alternatingSubmodule f U F p).subtype

/-- Two consecutive Čech differentials compose to zero. -/
theorem cechModuleDiff_comp (p : ℕ) :
    cechModuleDiff f U F p ≫ cechModuleDiff f U F (p + 1) = 0 := by
  ext s
  exact CechCochains.cechD_cechD U F.presheaf p s

/-- Two consecutive alternating Čech differentials compose to zero. -/
theorem alternatingCechModuleDiff_comp (p : ℕ) :
    alternatingCechModuleDiff f U F p ≫ alternatingCechModuleDiff f U F (p + 1) = 0 := by
  ext s
  exact Subtype.ext (CechCochains.cechD_cechD U F.presheaf p s.1)

/-- The usual Čech complex of a sheaf of modules, as a complex of `A`-modules. -/
def cechModuleComplex : CochainComplex (ModuleCat.{u} A) ℕ :=
  CochainComplex.of (cechModuleObj f U F) (cechModuleDiff f U F) (cechModuleDiff_comp f U F)

/-- The alternating Čech complex of a sheaf of modules, as a complex of `A`-modules. -/
def alternatingCechModuleComplex : CochainComplex (ModuleCat.{u} A) ℕ :=
  CochainComplex.of (alternatingCechModuleObj f U F) (alternatingCechModuleDiff f U F)
    (alternatingCechModuleDiff_comp f U F)

/-- The degree-`p` term of the usual Čech complex of `A`-modules is the module of all Čech
cochains. -/
@[simp]
theorem cechModuleComplex_X (p : ℕ) :
    (cechModuleComplex f U F).X p = cechModuleObj f U F p := rfl

/-- The degree-`p` term of the alternating Čech complex of `A`-modules is the module of
alternating Čech cochains. -/
@[simp]
theorem alternatingCechModuleComplex_X (p : ℕ) :
    (alternatingCechModuleComplex f U F).X p = alternatingCechModuleObj f U F p := rfl

/-- The consecutive differentials of the usual Čech complex of `A`-modules. -/
@[simp]
theorem cechModuleComplex_d (p : ℕ) :
    (cechModuleComplex f U F).d p (p + 1) = cechModuleDiff f U F p :=
  CochainComplex.of_d _ _ p

/-- The consecutive differentials of the alternating Čech complex of `A`-modules. -/
@[simp]
theorem alternatingCechModuleComplex_d (p : ℕ) :
    (alternatingCechModuleComplex f U F).d p (p + 1) = alternatingCechModuleDiff f U F p :=
  CochainComplex.of_d _ _ p

/-! ### Forgetting the module structures -/

/-- Forgetting the module structures in the usual Čech complex of `A`-modules recovers the
Čech complex of abelian groups. -/
def cechModuleComplex_forget :
    ((forget₂ (ModuleCat.{u} A) Ab).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (cechModuleComplex f U F) ≅
      cechComplex U F.presheaf :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    rintro p q (rfl : p + 1 = q)
    simp only [Iso.refl_hom, Functor.mapHomologicalComplex_obj_d, cechModuleComplex_d,
      cechComplex_d]
    rfl)

/-- Forgetting the module structures in the alternating Čech complex of `A`-modules recovers
the alternating Čech complex of abelian groups of Stacks 01FH. -/
def alternatingCechModuleComplex_forget :
    ((forget₂ (ModuleCat.{u} A) Ab).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (alternatingCechModuleComplex f U F) ≅
      alternatingCechComplex U F.presheaf :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    rintro p q (rfl : p + 1 = q)
    simp only [Iso.refl_hom, Functor.mapHomologicalComplex_obj_d,
      alternatingCechModuleComplex_d, alternatingCechComplex_d]
    rfl)

/-- **The scalar action on an ordinary Čech cochain is the action on sections induced by the
structural map to the affine base.** Read in the Čech complex of abelian groups — that is,
after forgetting the module structures, where the degree-`p` term is literally the group of
cochains — multiplication by `a : A` acts on the value at a tuple `i` by the section
`f.appLE ⊤ (inter U i) _ (toSpecΓ _ a)` of `𝒪_X` over that intersection.

This pins the `A`-module structure of `Stacks.Cech.cechModuleComplex` to `f`: the statement
mentions no auxiliary definition of this file, only `f.appLE` and `toSpecΓ`. -/
theorem cechModuleComplex_smul_eval (p : ℕ) (a : A) (s : (cechModuleComplex f U F).X p)
    (i : Fin (p + 1) → I) :
    ((cechModuleComplex_forget f U F).hom.f p).hom (a • s) i =
      (f.appLE ⊤ (CechCochains.inter U i) (by simp)).hom ((toSpecΓ (CommRingCat.of A)).hom a) •
        ((cechModuleComplex_forget f U F).hom.f p).hom s i :=
  rfl

/-! ### The `A`-linear alternating-to-usual comparison -/

/-- The `A`-linear alternating-to-usual Čech comparison: in each degree the inclusion of the
submodule of alternating cochains. -/
def alternatingCechModuleComplex_inclusion :
    alternatingCechModuleComplex f U F ⟶ cechModuleComplex f U F :=
  CochainComplex.ofHom (fun p => alternatingCechModuleSubtype f U F p) (fun p => by
    rw [cechModuleComplex_d, alternatingCechModuleComplex_d]
    ext s
    rfl)

/-- In every degree the `A`-linear comparison is the inclusion of the submodule of alternating
cochains. -/
@[simp]
theorem alternatingCechModuleComplex_inclusion_f (p : ℕ) :
    (alternatingCechModuleComplex_inclusion f U F).f p = alternatingCechModuleSubtype f U F p :=
  rfl

/-- The same evaluation formula on the alternating subcomplex: an alternating cochain is a
cochain, and the scalar action on it is again the action through the structural map. -/
theorem alternatingCechModuleComplex_smul_eval (p : ℕ) (a : A)
    (s : (alternatingCechModuleComplex f U F).X p) (i : Fin (p + 1) → I) :
    (((alternatingCechModuleComplex_forget f U F).hom.f p).hom (a • s)).1 i =
      (f.appLE ⊤ (CechCochains.inter U i) (by simp)).hom ((toSpecΓ (CommRingCat.of A)).hom a) •
        (((alternatingCechModuleComplex_forget f U F).hom.f p).hom s).1 i :=
  rfl

/-- Forgetting the module structures, the `A`-linear comparison is the canonical inclusion of
the alternating Čech complex into the usual one of Stacks 01FH. -/
theorem alternatingCechModuleComplex_inclusion_forget :
    (alternatingCechModuleComplex_forget f U F).inv ≫
        ((forget₂ (ModuleCat.{u} A) Ab).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (alternatingCechModuleComplex_inclusion f U F) ≫
        (cechModuleComplex_forget f U F).hom =
      alternatingCechInclusion U F.presheaf := by
  ext p s
  rfl

/-! ### Boundedness -/

/-- For a finite index type there are no nonzero alternating cochains in degrees at least the
cardinality of the index type: every tuple then repeats an index. -/
theorem subsingleton_alternatingSubmodule [Fintype I] {m : ℕ} (hm : Fintype.card I ≤ m) :
    Subsingleton (alternatingCechModuleObj f U F m) := by
  have hzero : ∀ s : CechCochains.Cochain U F.presheaf m,
      CechCochains.IsAlternating U F.presheaf s → s = 0 := by
    intro s hs
    funext i
    refine hs.1 i fun hi => ?_
    have := Fintype.card_le_of_injective i hi
    simp only [Fintype.card_fin] at this
    omega
  exact ⟨fun s t => Subtype.ext ((hzero _ s.2).trans (hzero _ t.2).symm)⟩

/-- **A finite family of opens gives an alternating Čech complex that vanishes in high
degrees.** It is zero in every degree at least the cardinality of the index type. -/
@[ega "III 6.6.2" "partial"]
theorem alternatingCechModuleComplex_bounded [Finite I] :
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m → IsZero ((alternatingCechModuleComplex f U F).X m) := by
  let := Fintype.ofFinite I
  refine ⟨Fintype.card I, fun m hm => ?_⟩
  rw [alternatingCechModuleComplex_X]
  have := subsingleton_alternatingSubmodule f U F hm
  exact ModuleCat.isZero_of_subsingleton _

end Stacks.Cech

end

end
