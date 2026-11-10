module

public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.SheafSubmodule
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.FlatOverLocalBase
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeBaseChange
public import StacksFrontier.AlgebraicGeometry.RegularSequence.ExtVanishing

/-!
# The direct-sum decomposition of `Iⁿ F_(n+1)` over a Noetherian local base

This file closes the hypothesis `hdec` of the file
`StacksFrontier/AlgebraicGeometry/FormalGeometry/AlgebraizationCoherentFormal/`
`FlatOverLocalBase.lean`:
in the situation of Stacks 0EJU — a Noetherian local ring `(R, 𝔪)` with `R → A`, `I = 𝔪 A`, and
the formal stalks of a coherent `I`-adic system `(F_n)` on `U` flat over `R` — the subsheaf
`Iⁿ⁺¹ F_(n+2)` of `Stacks.Algebraization.idealPowerSub` *is* a finite direct sum of copies of
`F_1`.

What `FlatOverLocalBase` already had was the stalkwise statement, one point at a time and with no
morphism of sheaves behind it. The morphism is built here, and it is the source's: choose
`a₁, …, a_k ∈ 𝔪ⁿ⁺¹` whose classes are a `κ`-basis of `𝔪ⁿ⁺¹/𝔪ⁿ⁺²`; multiplication by the image
of `aᵢ` in `A` carries `F_(n+1)` into `Iⁿ⁺¹ F_(n+1)` and kills `I F_(n+1)`, because
`I^(n+2) F_(n+1) = 0`, so it factors through `F_(n+1)/I F_(n+1) = F_1`; the `k` maps so obtained
assemble into `⨁_{i<k} F_1 ⟶ Iⁿ⁺¹ F_(n+1)`.

## Main definitions

* `Stacks.Algebraization.sectionSmul` — multiplication by a global function, as an endomorphism of
  a sheaf of `𝒪_X`-modules.
* `Stacks.Algebraization.sectionSmulTop` — the same, read as a morphism into the subsheaf
  `ℐᵉ M` when the function's restrictions lie in `ℐᵏ` with `e ≤ k`.
* `Stacks.Algebraization.idealPowerDesc` — **the morphism** `⨁_{i<κ} N ⟶ ℐᵏ M` attached to a
  family of such functions, where `N` is the quotient `M/ℐM`.
* `Stacks.Algebraization.stalkOfTuple` — a tuple of stalk elements, read in the stalk of a
  finite direct sum.

## Main results

* `Stacks.Algebraization.exists_quotientZeroIso` — the identification `F_m/I F_m ≅ F_0` for
  *every* `m`, not only `m = 1`, compatibly with the transition map.
* `Stacks.Algebraization.exists_quotientIso` — the same at every index: `F_m/Iᵈ⁺¹ F_m ≅ F_d`
  for `d ≤ m`, compatibly with the transition map.
* `Stacks.Algebraization.exists_transitionSmulUp` — **the up maps**: multiplication by a global
  function whose restrictions lie in `Iᵏ` is a map `F_d ⟶ F_m` for `d ≤ m ≤ d + k`, whose
  composites with the transition `F_m ⟶ F_d` are that multiplication on either side. These are
  what a non-principal `I` has in place of the splittings of Stacks 0DXW, and they are the
  index-raising action the graded form of Cohomology 0GYK consumes.
* `Stacks.Algebraization.sectionSmul_eq_zero` and
  `Stacks.Algebraization.idealPow_smul_globalSections_eq_bot` — multiplication by a function
  whose restrictions lie in `Iᵏ` is zero on a module annihilated by `Iᵏ`, and in particular
  `Iⁿ⁺¹` annihilates the `A`-module `H⁰(U, F_(n+1))`. This is the annihilation hypothesis both
  the Mittag-Leffler argument and the limit-topology argument for a general `I` ask for.
* `Stacks.Algebraization.ker_stalk_transition_zero` — the transition `F_m ⟶ F_0` is surjective on
  stalks with kernel `ℐ_y F_(m,y)`, for every `m`.
* `Stacks.Algebraization.stalk_idealPowerDesc_apply` — the stalk map of
  `Stacks.Algebraization.idealPowerDesc` is `(v_i) ↦ ∑ bᵢ · w_i` for any lifts `w_i` of the
  `v_i` along `M ⟶ M/ℐM`.
* `Stacks.Algebraization.bijective_stalk_idealPowerDesc` — those stalk maps are bijective in the
  situation of Stacks 0EJU.
* `Stacks.Algebraization.exists_isIso_idealPowerDesc` and
  `Stacks.Algebraization.exists_isoDirectSum_idealPowerSub` — **`hdec`**: for every `n` there is a
  `k` with `⨁_{i<k} F_1 ≅ Iⁿ⁺¹ F_(n+2)`, the first form keeping the morphism.
* `Stacks.Algebraization.finite_idealPowerSections_of_flatLocalBase` — every `H⁰(U, Iⁿ F_(n+1))`
  is a finite `A`-module. Stacks 0EJU itself is
  `Stacks.Algebraization.canonicallyExtends_of_flatLocalBase` in
  `FlatLocalBaseCanonicalExtension.lean` of this directory.

## Implementation notes

**Where the flatness goes in.** It is confined to
`Stacks.Flatness.exists_lift_basis_smul_of_flat_tower`, which produces the `aᵢ` and the two
statements a bijectivity argument needs: a tuple `(mᵢ)` of elements of the formal stalk with
`∑ aᵢ mᵢ ∈ 𝔪ⁿ⁺² F_y^∧` has every `mᵢ` in `𝔪 F_y^∧`, and every element of `𝔪ⁿ⁺¹ F_y^∧` is such a
combination modulo `𝔪ⁿ⁺² F_y^∧`. Those are stated with no quotients and no tensor products, which
is what lets them be transported to the stalks of the terms of `(F_n)` along
`Stacks.Algebraization.completedStalkQuotientEquivStalk`: the transport is by a single
`𝒪_{U,y}`-linear surjection `F_y^∧ → F_(n+1,y)`, and multiplication by `aᵢ` commutes with it
because `aᵢ` acts through `R → A → 𝒪_{U,y}`.

**Why `F_m/I F_m ≅ F_0` is available.** The third clause of
`Stacks.Coherent.IsCoherentAdicSystem` only identifies `F_(m+1)/Iᵐ⁺¹ F_(m+1)` with `F_m`, one
step at a time, and the kernel of a composite of transitions is not the composite of the kernels.
What gives the non-adjacent statement is
`Stacks.Coherent.IsCoherentAdicSystem.isIso_idealPowerQuotientMap_map`: the transition
`F_m ⟶ F_0` becomes invertible after dividing both sides by `I`, and `I F_0 = 0`, so its source
`F_m/I F_m` is already `F_0`. That is `Stacks.Algebraization.exists_quotientZeroIso`, whose
second component says the composite with the quotient projection is the transition — which is all
the stalk computation uses.

**Off the support of `I 𝒪_U` both sides vanish.** The flatness hypothesis of the source is only
made at the points of `U ∩ Y`, so the stalk map has to be shown bijective elsewhere for a
different reason: at `y ∉ supp(I 𝒪_U)` the stalk `ℐ_y` is the unit ideal, and
`Iᵐ F_(m-1) = 0` then forces every `F_(m,y)` to vanish. Both sides of the decomposition are zero
and there is nothing to check. `Stacks.Algebraization.eq_zero_stalk_of_notMem_support` is that
vanishing, obtained from a section of `ℐ` with a unit germ
(`Stacks.Algebraization.exists_mem_ideal_isUnit_germ_of_notMem_support`).

**Where this is used.** The decomposition is what makes the graded modules
`⨁ₙ Hᵖ(U, Iⁿ F_(n+1))` generated in degree zero, which is the chain condition the proofs of
conditions (a) and (b) of Stacks 0EHH need; see `FlatLocalBaseShifts.lean` and
`FlatLocalBaseCanonicalExtension.lean` of this directory.

## References

* [Stacks Project, Tag 0EJU](https://stacks.math.columbia.edu/tag/0EJU)
* [Stacks Project, Tag 0EJS](https://stacks.math.columbia.edu/tag/0EJS)
* [Stacks Project, Tag 0EHH](https://stacks.math.columbia.edu/tag/0EHH)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.ModuleSkyscraper
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

attribute [local instance] hasFiniteBiproducts_schemeModules

/-! ### Multiplication by a global function

Everything in this section is stated for an arbitrary scheme and ideal sheaf; the situation of
Stacks 0EJU enters only in the last two sections.

The identities below are proved in term mode, with the category of modules pinned by an
ascription `(P.ι : (P.toSheafOfModules : X.Modules) ⟶ M)` and by `(C := X.Modules)`. That is the
idiom the rest of this corner of the library uses, and it is not stylistic: `X.ringCatSheaf` has
type `TopCat.Sheaf RingCat ↑X.toPresheafedSpace` where
`SheafOfModules.Submodule.toSheafOfModules` asks for `Sheaf (Opens.grothendieckTopology ↥X)
RingCat`, and although those are the same type, a goal mentioning a subsheaf is then not
type-correct at `implicit` transparency, so `rw` refuses it and a `0` morphism between such
objects is not synthesised.
-/

variable {X : Scheme.{u}} {J : X.IdealSheafData}

/-- Multiplication by a global function on `X`, as an endomorphism of a sheaf of
`𝒪_X`-modules. -/
def sectionSmul (b : Γ(X, ⊤)) (M : X.Modules) : M ⟶ M :=
  (Stacks.RegularSequence.globalSmulCenter X b).app M

/-- On sections over `W`, `sectionSmul b M` is multiplication by the restriction of `b` to `W`. -/
theorem sectionSmul_app (b : Γ(X, ⊤)) (M : X.Modules) (W : X.Opens) (m : Γ(M, W)) :
    Scheme.Modules.Hom.app (sectionSmul b M) W m = X.presheaf.map W.leTop.op b • m :=
  rfl

/-- The hypothesis on a global function that the construction below needs: its restriction to
every affine open lies in the `k`-th power of the ideal there. -/
def RestrictMemIdealPow (J : X.IdealSheafData) (k : ℕ) (b : Γ(X, ⊤)) : Prop :=
  ∀ V : X.affineOpens,
    (X.presheaf.map (homOfLE (le_top (a := V.1))).op).hom b ∈ J.ideal V ^ k

/-- Multiplication by a function whose restrictions lie in `ℐᵏ` carries the subsheaf `ℐᵈ M`
into `ℐᵉ M` whenever `e ≤ k + d`. This is the only place the hypothesis on the function is
used. -/
theorem idealPowerMultiple_le_comap_sectionSmul (M : X.Modules) [M.IsQuasicoherent]
    {k d e : ℕ} (he : e ≤ k + d) {b : Γ(X, ⊤)} (hb : RestrictMemIdealPow J k b) :
    idealPowerMultiple J d M ≤
      sheafSubmoduleComap (sectionSmul b M) (idealPowerMultiple J e M) := by
  rw [idealPowerMultiple_le_iff]
  intro W x hx
  have hbx : (X.presheaf.map W.1.leTop.op).hom b • x ∈
      J.ideal W ^ (k + d) • (⊤ : Submodule Γ(X, W.1) Γ(M, W.1)) := by
    rw [pow_add, mul_smul]
    exact Submodule.smul_mem_smul (hb W) hx
  change (X.presheaf.map W.1.leTop.op).hom b • x ∈
    (idealPowerMultiple J e M).toSubmodule.obj (op W.1)
  exact Stacks.AlgebraicGeometry.IdealPower.le_idealPowerMultiple_obj J e M W
    (Submodule.smul_mono_left (Ideal.pow_le_pow_right he) hbx)

/-- Multiplication by a function whose restrictions lie in `ℐᵏ` carries all of `M` into
`ℐᵉ M` for `e ≤ k`. -/
theorem top_le_comap_sectionSmul (M : X.Modules) {k e : ℕ} (he : e ≤ k) {b : Γ(X, ⊤)}
    (hb : RestrictMemIdealPow J k b) :
    (⊤ : M.Submodule) ≤ sheafSubmoduleComap (sectionSmul b M) (idealPowerMultiple J e M) := by
  refine ge_of_eq (sheafSubmodule_eq_top_of_affine _ fun W x _ => ?_)
  have hbx : (X.presheaf.map W.1.leTop.op).hom b • x ∈
      J.ideal W ^ k • (⊤ : Submodule Γ(X, W.1) Γ(M, W.1)) :=
    Submodule.smul_mem_smul (hb W) Submodule.mem_top
  change (X.presheaf.map W.1.leTop.op).hom b • x ∈
    (idealPowerMultiple J e M).toSubmodule.obj (op W.1)
  exact Stacks.AlgebraicGeometry.IdealPower.le_idealPowerMultiple_obj J e M W
    (Submodule.smul_mono_left (Ideal.pow_le_pow_right he) hbx)

/-- **Multiplication by a function whose restrictions lie in `ℐᵏ`, as a morphism
`M ⟶ ℐᵉ M`** for `e ≤ k`. -/
def sectionSmulTop (M : X.Modules) {k e : ℕ} (he : e ≤ k) {b : Γ(X, ⊤)}
    (hb : RestrictMemIdealPow J k b) : M ⟶ (idealPowerMultiple J e M).toSheafOfModules :=
  (sheafTopIso M).inv ≫
    sheafSubmoduleMap (sectionSmul b M) ⊤ (idealPowerMultiple J e M)
      (top_le_comap_sectionSmul M he hb)

/-- `sectionSmulTop M he hb` followed by the inclusion of `ℐᵉ M` into `M` is `sectionSmul b M`. -/
@[simp]
theorem sectionSmulTop_comp_ι (M : X.Modules) {k e : ℕ} (he : e ≤ k) {b : Γ(X, ⊤)}
    (hb : RestrictMemIdealPow J k b) :
    sectionSmulTop M he hb ≫ (idealPowerMultiple J e M).ι = sectionSmul b M := by
  have h1 : sectionSmulTop M he hb ≫ (idealPowerMultiple J e M).ι =
      (sheafTopIso M).inv ≫ (sheafSubmoduleMap (sectionSmul b M) ⊤ (idealPowerMultiple J e M)
        (top_le_comap_sectionSmul M he hb) ≫ (idealPowerMultiple J e M).ι) :=
    Category.assoc _ _ _
  rw [h1, sheafSubmoduleMap_comp_ι]
  exact (sheafTopIso M).inv_comp_eq.2 rfl

/-- If a subsheaf `P` of `M` lies in the preimage of `⊥` under `sectionSmul b M`, the
multiplication vanishes on its sections. -/
private theorem sectionSmul_app_eq_zero_of_le_comap_bot (M : X.Modules) {b : Γ(X, ⊤)}
    {P : M.Submodule} (hle : P ≤ sheafSubmoduleComap (sectionSmul b M) (⊥ : M.Submodule))
    (U : (TopologicalSpace.Opens X)ᵒᵖ) (z : M.val.obj U) (hz : z ∈ P.toSubmodule.obj U) :
    ((sectionSmul b M).val.app U).hom z = 0 :=
  (Submodule.mem_bot _).mp
    ((SheafOfModules.Submodule.bot_obj M U).le (SheafOfModules.Submodule.le_iff.mp hle U hz))

/-- Multiplication by a function whose restrictions lie in `ℐᵏ` kills the subsheaf `ℐ M` of a
module annihilated by `ℐᵏ⁺¹`. -/
theorem idealPowerMultiple_one_ι_comp_sectionSmul (M : X.Modules) [M.IsQuasicoherent] (k : ℕ)
    (hbot : idealPowerMultiple J (k + 1) M = ⊥) {b : Γ(X, ⊤)}
    (hb : RestrictMemIdealPow J k b) :
    ((idealPowerMultiple J 1 M).ι :
        ((idealPowerMultiple J 1 M).toSheafOfModules : X.Modules) ⟶ M) ≫ sectionSmul b M =
      (0 : ((idealPowerMultiple J 1 M).toSheafOfModules : X.Modules) ⟶ _) := by
  have hle := idealPowerMultiple_le_comap_sectionSmul M (k := k) (d := 1) (e := k + 1)
    (le_refl _) hb
  rw [hbot] at hle
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  ext x
  exact sectionSmul_app_eq_zero_of_le_comap_bot M hle (op V) x.1 x.property

/-- Multiplication by a function whose restrictions lie in `ℐᵏ`, read as a morphism into
`ℐᵏ M`, kills the subsheaf `ℐ M`. -/
theorem idealPowerMultiple_one_ι_comp_sectionSmulTop (M : X.Modules) [M.IsQuasicoherent] (k : ℕ)
    (hbot : idealPowerMultiple J (k + 1) M = ⊥) {b : Γ(X, ⊤)}
    (hb : RestrictMemIdealPow J k b) :
    ((idealPowerMultiple J 1 M).ι :
        ((idealPowerMultiple J 1 M).toSheafOfModules : X.Modules) ⟶ M) ≫
      sectionSmulTop M (le_refl k) hb =
      (0 : ((idealPowerMultiple J 1 M).toSheafOfModules : X.Modules) ⟶ _) := by
  refine cancel_sheafSubmodule_ι (idealPowerMultiple J k M) _ _ ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun φ => ((idealPowerMultiple J 1 M).ι :
      ((idealPowerMultiple J 1 M).toSheafOfModules : X.Modules) ⟶ M) ≫ φ)
    (sectionSmulTop_comp_ι M (le_refl k) hb)) ?_
  exact (idealPowerMultiple_one_ι_comp_sectionSmul M k hbot hb).trans zero_comp.symm

/-- The morphism `M/ℐM ⟶ ℐᵏ M` attached to a function whose restrictions lie in `ℐᵏ`, for `M`
annihilated by `ℐᵏ⁺¹`: multiplication by the function factors through `M/ℐM`, and `e`
identifies that quotient with `N`. -/
def idealPowerComponent (M : X.Modules) [M.IsQuasicoherent] (k : ℕ)
    (hbot : idealPowerMultiple J (k + 1) M = ⊥) {b : Γ(X, ⊤)}
    (hb : RestrictMemIdealPow J k b) {N : X.Modules}
    (e : idealPowerQuotient J 1 M ≅ N) : N ⟶ (idealPowerMultiple J k M).toSheafOfModules :=
  e.inv ≫ cokernel.desc _ (sectionSmulTop M (le_refl k) hb)
    (idealPowerMultiple_one_ι_comp_sectionSmulTop M k hbot hb)

/-- The defining property of `Stacks.Algebraization.idealPowerComponent`: precomposed with the
projection `M ⟶ N` and postcomposed with the inclusion of `ℐᵏ M` into `M`, it is multiplication
by the function. -/
theorem comp_idealPowerComponent_comp_ι (M : X.Modules) [M.IsQuasicoherent] (k : ℕ)
    (hbot : idealPowerMultiple J (k + 1) M = ⊥) {b : Γ(X, ⊤)}
    (hb : RestrictMemIdealPow J k b) {N : X.Modules}
    (e : idealPowerQuotient J 1 M ≅ N) {t : M ⟶ N}
    (ht : cokernel.π (C := X.Modules) (idealPowerMultiple J 1 M).ι ≫ e.hom = t) :
    t ≫ idealPowerComponent M k hbot hb e ≫ (idealPowerMultiple J k M).ι =
      sectionSmul b M := by
  subst ht
  have hD : e.hom ≫ idealPowerComponent M k hbot hb e =
      cokernel.desc (idealPowerMultiple J 1 M).ι (sectionSmulTop M (le_refl k) hb)
        (idealPowerMultiple_one_ι_comp_sectionSmulTop M k hbot hb) :=
    Iso.hom_inv_id_assoc e _
  have h2 : (cokernel.π (C := X.Modules) (idealPowerMultiple J 1 M).ι ≫ e.hom) ≫
      idealPowerComponent M k hbot hb e = sectionSmulTop M (le_refl k) hb :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun φ => cokernel.π (C := X.Modules) (idealPowerMultiple J 1 M).ι ≫ φ)
        hD).trans (cokernel.π_desc _ _ _))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun φ => φ ≫ (idealPowerMultiple J k M).ι) h2).trans
      (sectionSmulTop_comp_ι M (le_refl k) hb))

/-- **The morphism `⨁_{i<κ} N ⟶ ℐᵏ M`** attached to a family of global functions whose
restrictions lie in `ℐᵏ`. -/
def idealPowerDesc (M : X.Modules) [M.IsQuasicoherent] (k : ℕ)
    (hbot : idealPowerMultiple J (k + 1) M = ⊥) {κ : ℕ} {b : Fin κ → Γ(X, ⊤)}
    (hb : ∀ i, RestrictMemIdealPow J k (b i)) {N : X.Modules}
    (e : idealPowerQuotient J 1 M ≅ N) :
    (⨁ fun _ : Fin κ => N) ⟶ (idealPowerMultiple J k M).toSheafOfModules :=
  biproduct.desc fun i => idealPowerComponent M k hbot (hb i) e

/-- `idealPowerDesc` is the biproduct descent of the components `idealPowerComponent`. -/
theorem idealPowerDesc_eq (M : X.Modules) [M.IsQuasicoherent] (k : ℕ)
    (hbot : idealPowerMultiple J (k + 1) M = ⊥) {κ : ℕ} {b : Fin κ → Γ(X, ⊤)}
    (hb : ∀ i, RestrictMemIdealPow J k (b i)) {N : X.Modules}
    (e : idealPowerQuotient J 1 M ≅ N) :
    idealPowerDesc M k hbot hb e =
      biproduct.desc fun i => idealPowerComponent M k hbot (hb i) e :=
  rfl

/-! ### The stalk maps of the morphism -/

/-- The stalk functor on a composite, read on an element. Stated for abstract modules so that
its proof may be a `rw` chain. -/
theorem stalk_comp_apply (y : X) {A B C : X.Modules} (f : A ⟶ B) (g : B ⟶ C)
    (a : (modulesStalkFunctor X y).obj A) :
    ((modulesStalkFunctor X y).map (C := X.Modules) g).hom
        (((modulesStalkFunctor X y).map (C := X.Modules) f).hom a) =
      ((modulesStalkFunctor X y).map (C := X.Modules) (f ≫ g)).hom a := by
  rw [Functor.map_comp, ModuleCat.hom_comp]
  rfl

/-- A tuple of elements of the stalk of `N`, assembled into an element of the stalk of the direct
sum of `κ` copies of `N` by the inclusions of the summands.

The stalk functor is additive, so this is a bijection onto the stalk of the direct sum; it is
used instead of an isomorphism with the module of tuples because `ModuleCat.biproductIsoPi` asks
for the `ModuleCat` structure on the module of tuples, which instance search does not find for
the stalk functor's values. -/
def stalkOfTuple (y : X) {κ : ℕ} (N : X.Modules)
    (v : Fin κ → ((modulesStalkFunctor X y).obj N)) :
    (modulesStalkFunctor X y).obj (⨁ fun _ : Fin κ => N) :=
  ∑ i, ((modulesStalkFunctor X y).map (C := X.Modules)
    (biproduct.ι (fun _ : Fin κ => N) i)).hom (v i)

/-- Every element of the stalk of a finite direct sum is
`Stacks.Algebraization.stalkOfTuple` of the tuple of its components: the stalk functor carries
the identity `∑ πᵢ ιᵢ = 𝟙` of `CategoryTheory.Limits.biproduct.total` to that statement. -/
theorem stalkOfTuple_stalk_π (y : X) {κ : ℕ} (N : X.Modules)
    (u : (modulesStalkFunctor X y).obj (⨁ fun _ : Fin κ => N)) :
    stalkOfTuple y N (fun i => ((modulesStalkFunctor X y).map (C := X.Modules)
      (biproduct.π (fun _ : Fin κ => N) i)).hom u) = u := by
  have htot : ∑ i : Fin κ, (biproduct.π (fun _ : Fin κ => N) i ≫
      biproduct.ι (fun _ : Fin κ => N) i) = 𝟙 (⨁ fun _ : Fin κ => N) := biproduct.total
  have hmap : (modulesStalkFunctor X y).map (C := X.Modules)
        (∑ i : Fin κ, (biproduct.π (fun _ : Fin κ => N) i ≫
          biproduct.ι (fun _ : Fin κ => N) i)) =
      ∑ i : Fin κ, (modulesStalkFunctor X y).map (C := X.Modules)
        (biproduct.π (fun _ : Fin κ => N) i ≫ biproduct.ι (fun _ : Fin κ => N) i) :=
    Functor.map_sum _ _ _
  have hid : (modulesStalkFunctor X y).map (C := X.Modules)
      (∑ i : Fin κ, (biproduct.π (fun _ : Fin κ => N) i ≫
        biproduct.ι (fun _ : Fin κ => N) i)) = 𝟙 _ := by
    rw [htot, CategoryTheory.Functor.map_id]
  have hsum : (∑ i : Fin κ, (modulesStalkFunctor X y).map (C := X.Modules)
      (biproduct.π (fun _ : Fin κ => N) i ≫ biproduct.ι (fun _ : Fin κ => N) i)) = 𝟙 _ :=
    hmap.symm.trans hid
  have happ := congrArg (fun φ : (modulesStalkFunctor X y).obj (⨁ fun _ : Fin κ => N) ⟶
    (modulesStalkFunctor X y).obj (⨁ fun _ : Fin κ => N) => φ.hom u) hsum
  refine Eq.trans ?_ (Eq.trans happ ?_)
  · rw [stalkOfTuple, ModuleCat.hom_sum]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_)
      (LinearMap.sum_apply Finset.univ (fun i : Fin κ =>
        ((modulesStalkFunctor X y).map (C := X.Modules)
          (biproduct.π (fun _ : Fin κ => N) i ≫
            biproduct.ι (fun _ : Fin κ => N) i)).hom) u).symm
    exact (stalk_comp_apply y (biproduct.π (fun _ : Fin κ => N) i)
      (biproduct.ι (fun _ : Fin κ => N) i) u)
  · rfl

/-- **The stalk of a morphism out of a finite biproduct, read on a tuple**: it is the sum of the
stalk maps of the components. -/
theorem stalk_biproduct_desc_stalkOfTuple (y : X) {κ : ℕ} {N P : X.Modules}
    (g : Fin κ → (N ⟶ P)) (v : Fin κ → ((modulesStalkFunctor X y).obj N)) :
    ((modulesStalkFunctor X y).map (C := X.Modules) (biproduct.desc g)).hom
        (stalkOfTuple y N v) =
      ∑ i, ((modulesStalkFunctor X y).map (C := X.Modules) (g i)).hom (v i) := by
  rw [stalkOfTuple, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [stalk_comp_apply y (biproduct.ι (fun _ : Fin κ => N) i) (biproduct.desc g) (v i),
    biproduct.ι_desc]

/-- Multiplication by a global function acts on a stalk as multiplication by its germ. -/
theorem stalk_sectionSmul_apply (b : Γ(X, ⊤)) (M : X.Modules) (y : X)
    (w : (modulesStalkFunctor X y).obj M) :
    ((modulesStalkFunctor X y).map (C := X.Modules) (sectionSmul b M)).hom w =
      (X.presheaf.germ ⊤ y trivial).hom b • w := by
  obtain ⟨V, hyV, t, ht⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf w
  rw [← ht, modulesStalkFunctor_map_germ (sectionSmul b M) y V hyV t]
  change (M.presheaf.germ V y hyV).hom ((X.presheaf.map V.leTop.op).hom b • t) = _
  rw [germ_smul y V hyV ((X.presheaf.map V.leTop.op).hom b) t,
    TopCat.Presheaf.germ_res_apply X.presheaf V.leTop y hyV b]

/-- **The stalk map of `Stacks.Algebraization.idealPowerDesc`, read inside the stalk of `M`.**
It sends the tuple of images of `w i` under the projection `M ⟶ N` to `∑ bᵢ · w i`.

This is the content of the globalization: the single morphism built from the `bᵢ` induces, at
every point at once, the map a decomposition argument on the stalks knows how to invert. -/
theorem stalk_idealPowerDesc_apply (M : X.Modules) [M.IsQuasicoherent] (k : ℕ)
    (hbot : idealPowerMultiple J (k + 1) M = ⊥) {κ : ℕ} {b : Fin κ → Γ(X, ⊤)}
    (hb : ∀ i, RestrictMemIdealPow J k (b i)) {N : X.Modules}
    (e : idealPowerQuotient J 1 M ≅ N) {t : M ⟶ N}
    (ht : cokernel.π (C := X.Modules) (idealPowerMultiple J 1 M).ι ≫ e.hom = t)
    (y : X) (w : Fin κ → ((modulesStalkFunctor X y).obj M)) :
    ((modulesStalkFunctor X y).map (C := X.Modules) (idealPowerMultiple J k M).ι).hom
        (((modulesStalkFunctor X y).map (C := X.Modules) (idealPowerDesc M k hbot hb e)).hom
          (stalkOfTuple y N
            (fun i => ((modulesStalkFunctor X y).map (C := X.Modules) t).hom (w i)))) =
      ∑ i, (X.presheaf.germ ⊤ y trivial).hom (b i) • w i := by
  have hd := stalk_biproduct_desc_stalkOfTuple y
    (fun i => idealPowerComponent M k hbot (hb i) e)
    (fun i => ((modulesStalkFunctor X y).map (C := X.Modules) t).hom (w i))
  refine Eq.trans (congrArg ((modulesStalkFunctor X y).map (C := X.Modules)
    (idealPowerMultiple J k M).ι).hom hd) ?_
  refine Eq.trans (map_sum ((modulesStalkFunctor X y).map (C := X.Modules)
    (idealPowerMultiple J k M).ι).hom _ Finset.univ) ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Eq.trans (congrArg ((modulesStalkFunctor X y).map (C := X.Modules)
      (idealPowerMultiple J k M).ι).hom
    (stalk_comp_apply y t (idealPowerComponent M k hbot (hb i) e) (w i))) ?_
  refine Eq.trans (stalk_comp_apply y (t ≫ idealPowerComponent M k hbot (hb i) e)
    (idealPowerMultiple J k M).ι (w i)) ?_
  refine Eq.trans (congrArg
    (fun φ => ((modulesStalkFunctor X y).map (C := X.Modules) φ).hom (w i))
    ((Category.assoc t (idealPowerComponent M k hbot (hb i) e)
      (idealPowerMultiple J k M).ι).trans
      (comp_idealPowerComponent_comp_ι M k hbot (hb i) e ht))) ?_
  exact stalk_sectionSmul_apply (b i) M y (w i)

/-! ### The quotient of a term by `ℐ` is the zeroth term -/

/-- The identification `F_m / ℐ^(d+1) F_m ≅ F_d` for `d ≤ m`, compatible with the transition. -/
private theorem exists_quotientIso_aux (G : Stacks.Coherent.CoherentAdicSystems J) {d m : ℕ}
    (h : d ≤ m) :
    ∃ e : idealPowerQuotient J (d + 1) (G.obj.obj (op m)) ≅ G.obj.obj (op d),
      cokernel.π (C := X.Modules) (idealPowerMultiple J (d + 1) (G.obj.obj (op m))).ι ≫ e.hom =
        G.obj.map (homOfLE h).op := by
  have h1 : IsIso (idealPowerQuotientMap J J (d + 1) (d + 1) le_rfl
      (G.obj.map (homOfLE h).op)) :=
    G.property.isIso_idealPowerQuotientMap_map J (d + 1) h le_rfl
  have h2 : IsIso (cokernel.π (C := X.Modules)
      (idealPowerMultiple J (d + 1) (G.obj.obj (op d))).ι) :=
    isIso_cokernel_π_of_idealPowerMultiple_eq_bot J (d + 1) _
      (G.property.idealPowerMultiple_eq_bot d)
  refine ⟨asIso (idealPowerQuotientMap J J (d + 1) (d + 1) le_rfl
      (G.obj.map (homOfLE h).op)) ≪≫
    (asIso (cokernel.π (C := X.Modules)
      (idealPowerMultiple J (d + 1) (G.obj.obj (op d))).ι)).symm, ?_⟩
  rw [Iso.trans_hom, asIso_hom, Iso.symm_hom, asIso_inv, ← Category.assoc,
    idealPowerQuotientMap_π, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- **The identification `F_m / ℐ F_m ≅ F_0`, for every `m`**, compatible with the transition
map of the system.

The third clause of `Stacks.Coherent.IsCoherentAdicSystem` gives this for `m = 1` only. For
general `m` it comes from
`Stacks.Coherent.IsCoherentAdicSystem.isIso_idealPowerQuotientMap_map`: the transition
`F_m ⟶ F_0` is invertible after dividing both sides by `ℐ`, and `ℐ F_0 = 0`, so the target of
that reduction is `F_0` itself. -/
theorem exists_quotientZeroIso (G : Stacks.Coherent.CoherentAdicSystems J) (m : ℕ) :
    ∃ e : idealPowerQuotient J 1 (G.obj.obj (op m)) ≅ G.obj.obj (op 0),
      cokernel.π (C := X.Modules) (idealPowerMultiple J 1 (G.obj.obj (op m))).ι ≫ e.hom =
        G.obj.map (homOfLE (Nat.zero_le m)).op := by
  exact exists_quotientIso_aux G (Nat.zero_le m)

/-! ### The up maps of a coherent adic system

Multiplication by a global function `b` whose restrictions lie in `ℐᵏ` runs *up* the system, in
the direction opposite to the transitions: it kills `ℐ^(d+1) F_m` whenever `ℐ^(k+d+1) F_m = 0`,
so it factors through `F_m / ℐ^(d+1) F_m`, which is `F_d`. The resulting `F_d ⟶ F_m` is the
general-ideal replacement for the splittings a principal `ℐ = (f)` provides, and it is what the
graded form of Cohomology 0GYK consumes: the degree-`k` part of `gr_ℐ(A)` acts on the system by
raising the index by `k`.
-/

/-- **The identification `F_m / ℐ^(d+1) F_m ≅ F_d` for every `d ≤ m`**, compatible with the
transition map of the system.

This is `Stacks.Algebraization.exists_quotientZeroIso` with the index `0` replaced by an
arbitrary `d`, by the same two steps: the transition `F_m ⟶ F_d` is invertible after dividing
both sides by `ℐ^(d+1)`
(`Stacks.Coherent.IsCoherentAdicSystem.isIso_idealPowerQuotientMap_map`), and `ℐ^(d+1) F_d = 0`,
so the target of that reduction is `F_d` itself. -/
theorem exists_quotientIso (G : Stacks.Coherent.CoherentAdicSystems J) {d m : ℕ} (h : d ≤ m) :
    ∃ e : idealPowerQuotient J (d + 1) (G.obj.obj (op m)) ≅ G.obj.obj (op d),
      cokernel.π (C := X.Modules) (idealPowerMultiple J (d + 1) (G.obj.obj (op m))).ι ≫ e.hom =
        G.obj.map (homOfLE h).op := by
  exact exists_quotientIso_aux G h

/-- Multiplication by a function whose restrictions lie in `ℐᵏ` kills the subsheaf `ℐᵈ M` of a
module annihilated by `ℐʳ`, for `r ≤ k + d`.

At `d = 1` and `r = k + 1` this is
`Stacks.Algebraization.idealPowerMultiple_one_ι_comp_sectionSmul`; the general `d` is what the
up maps below factor through. -/
theorem idealPowerMultiple_ι_comp_sectionSmul (M : X.Modules) [M.IsQuasicoherent]
    {k d r : ℕ} (hr : r ≤ k + d) (hbot : idealPowerMultiple J r M = ⊥) {b : Γ(X, ⊤)}
    (hb : RestrictMemIdealPow J k b) :
    ((idealPowerMultiple J d M).ι :
        ((idealPowerMultiple J d M).toSheafOfModules : X.Modules) ⟶ M) ≫ sectionSmul b M =
      (0 : ((idealPowerMultiple J d M).toSheafOfModules : X.Modules) ⟶ _) := by
  have hle := idealPowerMultiple_le_comap_sectionSmul M (k := k) (d := d) (e := r) hr hb
  rw [hbot] at hle
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  ext x
  exact sectionSmul_app_eq_zero_of_le_comap_bot M hle (op V) x.1 x.property

/-- Multiplication by a function whose restrictions lie in `ℐᵏ` is the zero endomorphism of a
module annihilated by `ℐᵏ`. -/
theorem sectionSmul_eq_zero (M : X.Modules) {k : ℕ} (hbot : idealPowerMultiple J k M = ⊥)
    {b : Γ(X, ⊤)} (hb : RestrictMemIdealPow J k b) : sectionSmul b M = 0 := by
  have hle := top_le_comap_sectionSmul M (le_refl k) hb
  rw [hbot] at hle
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  ext x
  exact sectionSmul_app_eq_zero_of_le_comap_bot M hle (op V) x
    ((sheafTop_obj (M := M) (op V)).ge Submodule.mem_top)

/-- **The up map of a coherent adic system.** Let `b` be a global function whose restrictions
lie in `ℐᵏ`, and let `d ≤ m ≤ d + k`. Multiplication by `b` on `F_m` kills `ℐ^(d+1) F_m`,
because `ℐ^(m+1) F_m = 0` and `m + 1 ≤ k + (d + 1)`, so it factors through
`F_m / ℐ^(d+1) F_m`, which is `F_d`. The factorization `u : F_d ⟶ F_m` composes with the
transition `F_m ⟶ F_d` to multiplication by `b` on either side.

This needs nothing of `b` beyond the membership of its restrictions in `ℐᵏ`, so it is available
for each of a family of generators of a non-principal `ℐ`. At `k = 1` and `m = d + 1` it is the
factorization half of condition (1) of Stacks 0H39, the input the Mittag-Leffler criterion
Stacks 0BLC runs on. -/
theorem exists_transitionSmulUp (G : Stacks.Coherent.CoherentAdicSystems J) {k d m : ℕ}
    (hdm : d ≤ m) (hmd : m ≤ d + k) {b : Γ(X, ⊤)} (hb : RestrictMemIdealPow J k b) :
    ∃ u : G.obj.obj (op d) ⟶ G.obj.obj (op m),
      G.obj.map (homOfLE hdm).op ≫ u = sectionSmul b (G.obj.obj (op m)) ∧
        u ≫ G.obj.map (homOfLE hdm).op = sectionSmul b (G.obj.obj (op d)) := by
  have hqc : (G.obj.obj (op m)).IsQuasicoherent := G.property.isQuasicoherent m
  obtain ⟨e, he⟩ := exists_quotientIso G hdm
  have hkill := idealPowerMultiple_ι_comp_sectionSmul (G.obj.obj (op m)) (k := k) (d := d + 1)
    (r := m + 1) (by omega) (G.property.idealPowerMultiple_eq_bot m) hb
  have h1 : G.obj.map (homOfLE hdm).op ≫
      (e.inv ≫ cokernel.desc _ (sectionSmul b (G.obj.obj (op m))) hkill) =
      sectionSmul b (G.obj.obj (op m)) := by
    rw [← he, Category.assoc, Iso.hom_inv_id_assoc]
    exact cokernel.π_desc _ _ _
  refine ⟨_, h1, ?_⟩
  have : Epi (G.obj.map (homOfLE hdm).op) := G.property.epi_map hdm
  rw [← cancel_epi (G.obj.map (homOfLE hdm).op), ← Category.assoc, h1]
  exact ((Stacks.RegularSequence.globalSmulCenter X b).naturality
    (G.obj.map (homOfLE hdm).op)).symm

/-- A transition map of a coherent adic system is surjective on stalks, at any pair of
indices. -/
theorem surjective_stalk_transition (G : Stacks.Coherent.CoherentAdicSystems J) (x : X)
    {d m : ℕ} (h : d ≤ m) :
    Function.Surjective ((modulesStalkFunctor X x).map (C := X.Modules)
      (G.obj.map (homOfLE h).op)).hom := by
  have : Epi (G.obj.map (homOfLE h).op) := G.property.epi_map h
  have : Epi ((modulesStalkFunctor X x).map (C := X.Modules) (G.obj.map (homOfLE h).op)) :=
    Functor.map_epi _ _
  exact (ModuleCat.epi_iff_surjective _).mp inferInstance

/-- **On stalks, the kernel of the transition `F_m ⟶ F_0` of a coherent adic system is
`ℐ_x F_(m,x)`**, for every `m`.

For `m = 1` this is `Stacks.Algebraization.ker_stalk_coherentAdicTransition`; the general case
runs the same argument with `Stacks.Algebraization.exists_quotientZeroIso` in place of the
adjacent identification. -/
theorem ker_stalk_transition_zero (G : Stacks.Coherent.CoherentAdicSystems J) (x : X) (m : ℕ) :
    LinearMap.ker ((modulesStalkFunctor X x).map (C := X.Modules)
        (G.obj.map (homOfLE (Nat.zero_le m)).op)).hom =
      IdealSheafData.stalk J x •
        (⊤ : Submodule (X.presheaf.stalk x)
          ((modulesStalkFunctor X x).obj (G.obj.obj (op m)))) := by
  have : (G.obj.obj (op m)).IsQuasicoherent := G.property.isQuasicoherent m
  obtain ⟨e, he⟩ := exists_quotientZeroIso G m
  have key : (modulesStalkFunctor X x).map (C := X.Modules)
        (G.obj.map (homOfLE (Nat.zero_le m)).op) =
      (modulesStalkFunctor X x).map (C := X.Modules)
          (cokernel.π (C := X.Modules) (idealPowerMultiple J 1 (G.obj.obj (op m))).ι) ≫
        (modulesStalkFunctor X x).map (C := X.Modules) e.hom := by
    rw [← Functor.map_comp]
    exact congrArg _ he.symm
  have : IsIso (C := X.Modules) e.hom := ⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩
  have : IsIso ((modulesStalkFunctor X x).map (C := X.Modules) e.hom) := Functor.map_isIso _ _
  have heker : LinearMap.ker ((modulesStalkFunctor X x).map (C := X.Modules) e.hom).hom = ⊥ :=
    LinearMap.ker_eq_bot.2 ((ModuleCat.mono_iff_injective _).mp inferInstance)
  rw [key, ModuleCat.hom_comp, LinearMap.ker_comp, heker, Submodule.comap_bot,
    ← range_stalk_submodule_ι_eq_ker_stalk_cokernel_π,
    stalk_idealPowerMultiple J 1 (G.obj.obj (op m)) x, pow_one]

/-! ### Off the support of the ideal sheaf -/

/-- Off the support of an ideal sheaf there is, on any affine open neighbourhood of the point, a
section of the ideal whose germ is a unit. -/
theorem exists_mem_ideal_isUnit_germ_of_notMem_support (J : X.IdealSheafData) {x : X}
    (hx : x ∉ J.support) (U : X.affineOpens) (hxU : x ∈ U.1) :
    ∃ f ∈ J.ideal U, IsUnit ((X.presheaf.germ U.1 x hxU).hom f) := by
  have hz : x ∉ X.zeroLocus (U := U.1) (J.ideal U) := fun h =>
    hx (Scheme.IdealSheafData.mem_support_iff_of_mem hxU |>.2 h)
  rw [Scheme.mem_zeroLocus_iff] at hz
  obtain ⟨f, hf, hfx⟩ := by simpa using hz
  exact ⟨f, hf, (Scheme.mem_basicOpen X f x hxU).1 hfx⟩

/-- **Off the support of `ℐ` every term of a coherent adic system has vanishing stalk.**

The `m`-th term is annihilated by `ℐᵐ⁺¹`, so the germ of a section of `ℐ` kills its stalk to the
power `m + 1`; off the support some such germ is a unit. -/
theorem eq_zero_stalk_of_notMem_support (G : Stacks.Coherent.CoherentAdicSystems J) {x : X}
    (hx : x ∉ J.support) (m : ℕ)
    (w : (modulesStalkFunctor X x).obj (G.obj.obj (op m))) : w = 0 := by
  obtain ⟨U, hxU, -⟩ := exists_affineOpen_mem_le x ⊤ trivial
  obtain ⟨f, hf, hfu⟩ := exists_mem_ideal_isUnit_germ_of_notMem_support J hx U hxU
  obtain ⟨V, hxV, t, ht⟩ :=
    TopCat.Presheaf.exists_germ_eq (G.obj.obj (op m)).presheaf w
  obtain ⟨W, hxW, hWle⟩ := exists_affineOpen_mem_le x (U.1 ⊓ V) ⟨hxU, hxV⟩
  have hWU : W.1 ≤ U.1 := hWle.trans inf_le_left
  have hWV : W.1 ≤ V := hWle.trans inf_le_right
  set fW : Γ(X, W.1) := (X.presheaf.map (homOfLE hWU).op).hom f with hfW
  have hfWmem : fW ∈ J.ideal W := by
    rw [hfW, ← Scheme.IdealSheafData.map_ideal (I := J) hWU]
    exact Ideal.mem_map_of_mem _ hf
  have hpow : fW ^ (m + 1) ∈ J.ideal W ^ (m + 1) := Ideal.pow_mem_pow hfWmem _
  have hzero : fW ^ (m + 1) •
      (G.obj.obj (op m)).presheaf.map (homOfLE hWV).op t = 0 :=
    smul_eq_zero_of_idealPowerMultiple_eq_bot J (m + 1) (G.obj.obj (op m))
      (G.property.idealPowerMultiple_eq_bot m) W hpow _
  have hgermsmul : ((G.obj.obj (op m)).presheaf.germ W.1 x hxW).hom
        (fW ^ (m + 1) • (G.obj.obj (op m)).presheaf.map (homOfLE hWV).op t) =
      (X.presheaf.germ W.1 x hxW).hom (fW ^ (m + 1)) •
        (show (modulesStalkFunctor X x).obj (G.obj.obj (op m)) from
          ((G.obj.obj (op m)).presheaf.germ W.1 x hxW).hom
            ((G.obj.obj (op m)).presheaf.map (homOfLE hWV).op t)) :=
    germ_smul x W.1 hxW _ _
  have hgermf : (X.presheaf.germ W.1 x hxW).hom (fW ^ (m + 1)) =
      ((X.presheaf.germ U.1 x hxU).hom f) ^ (m + 1) := by
    rw [hfW, ← map_pow, ← map_pow,
      TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hWU) x hxW]
  have hgermt : ((G.obj.obj (op m)).presheaf.germ W.1 x hxW).hom
      ((G.obj.obj (op m)).presheaf.map (homOfLE hWV).op t) = w :=
    (TopCat.Presheaf.germ_res_apply (G.obj.obj (op m)).presheaf (homOfLE hWV) x hxW t).trans ht
  have hkey : ((X.presheaf.germ U.1 x hxU).hom f) ^ (m + 1) • w = 0 := by
    rw [← hgermf, ← hgermt, ← hgermsmul, hzero, map_zero]
    rfl
  exact (hfu.pow (m + 1)).smul_eq_zero.1 hkey

/-! ### Bijectivity of the stalk maps in the situation of Stacks 0EJU -/

variable (S : AlgebraizationSituation.{u})
  (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))

/-- The global function on `U` determined by an element of `Iᵏ` has all its restrictions in the
`k`-th power of the ideal of `I 𝒪_U`. -/
theorem restrictMemIdealPow_scalarMap (k : ℕ) {a : S.A} (ha : a ∈ S.I ^ k) :
    RestrictMemIdealPow (idealOnOpen S) k (scalarMap S a) :=
  fun V => scalarMap_restrict_mem_idealOnOpen_pow S V k ha

/-- **`Iⁿ⁺¹` annihilates `H⁰(U, F_(n+1))`.** The term of index `n` of a coherent `I`-adic system
on the open complement is annihilated by `(I 𝒪_U)ⁿ⁺¹` as a sheaf, so the `(n+1)`-st power of `I`
annihilates its `A`-module of global sections on `U`.

This is the annihilation input of
`Stacks.Cohomology.IdealBoundaries.isMittagLefflerCategorical_of_idealBoundaries` for the system
of global sections, and the `hpow` input of
`Stacks.AdicLimit.iInf_induced_eq_adicModuleTopology` for the limit topology on the module of
compatible sections. -/
theorem idealPow_smul_globalSections_eq_bot (n : ℕ) :
    S.I ^ (n + 1) • (⊤ : Submodule S.A ((globalSectionsSystem S F).obj (op n))) = ⊥ := by
  refine le_antisymm (Submodule.smul_le.mpr fun a ha m _ => ?_) bot_le
  have hz := sectionSmul_eq_zero (F.obj.obj (op n)) (F.property.idealPowerMultiple_eq_bot n)
    (restrictMemIdealPow_scalarMap S (n + 1) ha)
  have hid : (S.U.toScheme.presheaf.map (⊤ : S.U.toScheme.Opens).leTop.op) (scalarMap S a) =
      scalarMap S a := by
    rw [show (⊤ : S.U.toScheme.Opens).leTop.op = 𝟙 _ from
      Quiver.Hom.unop_inj (Subsingleton.elim _ _), S.U.toScheme.presheaf.map_id]
    rfl
  refine (Submodule.mem_bot _).mpr ?_
  have h2 : ∀ x : Γ(F.obj.obj (op n), ⊤),
      (S.U.toScheme.presheaf.map (⊤ : S.U.toScheme.Opens).leTop.op) (scalarMap S a) • x =
        Scheme.Modules.Hom.app (sectionSmul (scalarMap S a) (F.obj.obj (op n)))
          (⊤ : S.U.toScheme.Opens) x := fun x => rfl
  have h3 : ∀ x : Γ(F.obj.obj (op n), ⊤), scalarMap S a • x = 0 := by
    intro x
    rw [← hid, h2 x]
    exact congrArg (fun φ => Scheme.Modules.Hom.app φ (⊤ : S.U.toScheme.Opens) x) hz |>.trans rfl
  exact h3 m

/-- **The stalk maps of `Stacks.Algebraization.idealPowerDesc` are bijective** when the global
functions come from representatives of a `κ`-basis of `𝔪ⁿ⁺¹/𝔪ⁿ⁺²`.

At a point of `U ∩ Y` this is the flatness argument
(`Stacks.Flatness.mem_smul_top_of_sum_smul_mem` and `Stacks.Flatness.exists_sum_smul_sub_mem`)
transported from the formal stalk `F_y^∧` to the stalk of `F_(n+1)` along the surjection
`F_y^∧ → F_(n+1,y)` of `Stacks.Algebraization.completedStalkQuotientEquivStalk`; off `U ∩ Y`
both sides vanish. -/
theorem bijective_stalk_idealPowerDesc (B : FlatLocalBase S F) (n : ℕ) {k : ℕ}
    [(F.obj.obj (op (n + 1))).IsQuasicoherent]
    (e₀ : (↥(IsLocalRing.maximalIdeal B.R ^ (n + 1)) ⧸
        (IsLocalRing.maximalIdeal B.R •
          (⊤ : Submodule B.R ↥(IsLocalRing.maximalIdeal B.R ^ (n + 1))))) ≃ₗ[B.R]
      (Fin k → (B.R ⧸ IsLocalRing.maximalIdeal B.R)))
    (r : Fin k → ↥(IsLocalRing.maximalIdeal B.R ^ (n + 1)))
    (hr : ∀ i, e₀.symm (Pi.single i (1 : B.R ⧸ IsLocalRing.maximalIdeal B.R)) =
      Submodule.Quotient.mk (r i))
    (hb : ∀ i, RestrictMemIdealPow (idealOnOpen S) (n + 1)
      (scalarMap S (B.φ ((r i : B.R)))))
    (hbot : idealPowerMultiple (idealOnOpen S) (n + 1 + 1) (F.obj.obj (op (n + 1))) = ⊥)
    (e : idealPowerQuotient (idealOnOpen S) 1 (F.obj.obj (op (n + 1))) ≅ F.obj.obj (op 0))
    (he : cokernel.π (C := S.U.toScheme.Modules)
        (idealPowerMultiple (idealOnOpen S) 1 (F.obj.obj (op (n + 1)))).ι ≫ e.hom =
      F.obj.map (homOfLE (Nat.zero_le (n + 1))).op)
    (y : S.U.toScheme) :
    Function.Bijective ((modulesStalkFunctor S.U.toScheme y).map (C := S.U.toScheme.Modules)
      (idealPowerDesc (F.obj.obj (op (n + 1))) (n + 1) hbot hb e)).hom := by
  classical
  have : IsLocallyNoetherian S.U.toScheme := isLocallyNoetherian_of_isOpenImmersion S.U.ι
  have hcoh : _root_.SheafOfModules.IsCoherent.{u} (F.obj.obj (op (n + 1))) :=
    F.property.1 (n + 1)
  have hmonoι : Mono (C := S.U.toScheme.Modules) (idealPowerSub S F n).ι :=
    (idealPowerShortComplex_shortExact S F n).mono_f
  have hiyinj : Function.Injective
      ((modulesStalkFunctor S.U.toScheme y).map (C := S.U.toScheme.Modules)
        (idealPowerSub S F n).ι).hom :=
    (ModuleCat.mono_iff_injective _).mp (Functor.map_mono _ _)
  have hiyrange : LinearMap.range ((modulesStalkFunctor S.U.toScheme y).map
        (C := S.U.toScheme.Modules) (idealPowerSub S F n).ι).hom =
      IdealSheafData.stalk (idealOnOpen S) y ^ (n + 1) •
        (⊤ : Submodule (S.U.toScheme.presheaf.stalk y)
          ((modulesStalkFunctor S.U.toScheme y).obj (F.obj.obj (op (n + 1))))) :=
    stalk_idealPowerMultiple (idealOnOpen S) (n + 1) (F.obj.obj (op (n + 1))) y
  have hgerm : ∀ i : Fin k,
      (S.U.toScheme.presheaf.germ ⊤ y trivial).hom (scalarMap S (B.φ ((r i : B.R)))) =
        germOfBase S y (B.φ ((r i : B.R))) := fun _ => rfl
  by_cases hy : y ∈ (idealOnOpen S).support
  · let : Algebra B.R (completedLocalRing (idealOnOpen S) y) :=
      ((baseToCompletedLocalRing S y).comp B.φ).toAlgebra
    let := completedStalkBaseModule S F y B.φ
    have : IsScalarTower B.R (completedLocalRing (idealOnOpen S) y)
        (completedStalk (idealOnOpen S) F y) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    have : Module.Flat B.R (completedStalk (idealOnOpen S) F y) := B.flat y hy
    have hJeq : (IsLocalRing.maximalIdeal B.R).map
          (algebraMap B.R (completedLocalRing (idealOnOpen S) y)) =
        completedLocalIdeal (idealOnOpen S) y := by
      rw [completedLocalIdeal_eq_map_baseToCompletedLocalRing, B.I_eq, Ideal.map_map]
      rfl
    obtain ⟨πL, hπL⟩ : ∃ f : completedStalk (idealOnOpen S) F y →ₗ[S.U.toScheme.presheaf.stalk y]
        ((modulesStalkFunctor S.U.toScheme y).obj (F.obj.obj (op (n + 1)))),
        ∀ z, f z = completedStalkQuotientEquivStalk F y (n + 1) (Submodule.Quotient.mk z) :=
      ⟨(completedStalkQuotientEquivStalk F y (n + 1)).toLinearMap ∘ₗ
          LinearMap.restrictScalars (S.U.toScheme.presheaf.stalk y)
            (Submodule.mkQ (completedLocalIdeal (idealOnOpen S) y ^ (n + 1 + 1) •
              (⊤ : Submodule (completedLocalRing (idealOnOpen S) y)
                (completedStalk (idealOnOpen S) F y)))),
        fun _ => rfl⟩
    have hπsurj : Function.Surjective πL := by
      intro m
      obtain ⟨q, hq⟩ := (completedStalkQuotientEquivStalk F y (n + 1)).surjective m
      obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ q
      exact ⟨z, by rw [hπL, hz, hq]⟩
    have hπker : ∀ z, πL z = 0 ↔ z ∈ completedLocalIdeal (idealOnOpen S) y ^ (n + 1 + 1) •
        (⊤ : Submodule (completedLocalRing (idealOnOpen S) y)
          (completedStalk (idealOnOpen S) F y)) := by
      intro z
      rw [hπL, LinearEquiv.map_eq_zero_iff]
      exact Submodule.Quotient.mk_eq_zero _
    have hRsmul : ∀ (i : Fin k) (z : completedStalk (idealOnOpen S) F y),
        ((r i : B.R)) • z = germOfBase S y (B.φ ((r i : B.R))) • z := by
      intro i z
      change ((baseToCompletedLocalRing S y).comp B.φ) ((r i : B.R)) • z = _
      rw [RingHom.comp_apply, baseToCompletedLocalRing_apply]
      exact algebraMap_smul _ _ _
    have hπcomb : ∀ z : Fin k → completedStalk (idealOnOpen S) F y,
        πL (∑ i, ((r i : B.R)) • z i) =
          ∑ i, germOfBase S y (B.φ ((r i : B.R))) • πL (z i) := by
      intro z
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [hRsmul i (z i), map_smul]
    have hπsmulmem : ∀ (I : Ideal (S.U.toScheme.presheaf.stalk y))
        (z : completedStalk (idealOnOpen S) F y),
        z ∈ I • (⊤ : Submodule (S.U.toScheme.presheaf.stalk y)
            (completedStalk (idealOnOpen S) F y)) →
          πL z ∈ I • (⊤ : Submodule (S.U.toScheme.presheaf.stalk y)
            ((modulesStalkFunctor S.U.toScheme y).obj (F.obj.obj (op (n + 1))))) := by
      intro I z hz
      refine Submodule.smul_induction_on hz ?_ ?_
      · intro c hc z₀ _
        rw [map_smul]
        exact Submodule.smul_mem_smul hc Submodule.mem_top
      · intro z₁ z₂ h₁ h₂
        rw [map_add]
        exact Submodule.add_mem _ h₁ h₂
    have hπpre : ∀ (I : Ideal (S.U.toScheme.presheaf.stalk y))
        (m : (modulesStalkFunctor S.U.toScheme y).obj (F.obj.obj (op (n + 1)))),
        m ∈ I • (⊤ : Submodule (S.U.toScheme.presheaf.stalk y)
            ((modulesStalkFunctor S.U.toScheme y).obj (F.obj.obj (op (n + 1))))) →
          ∃ z, πL z = m ∧ z ∈ I • (⊤ : Submodule (S.U.toScheme.presheaf.stalk y)
            (completedStalk (idealOnOpen S) F y)) := by
      intro I m hm
      refine Submodule.smul_induction_on hm ?_ ?_
      · intro c hc m₀ _
        obtain ⟨z₀, hz₀⟩ := hπsurj m₀
        exact ⟨c • z₀, by rw [map_smul, hz₀], Submodule.smul_mem_smul hc Submodule.mem_top⟩
      · rintro m₁ m₂ ⟨z₁, hz₁, hm₁⟩ ⟨z₂, hz₂, hm₂⟩
        exact ⟨z₁ + z₂, by rw [map_add, hz₁, hz₂], Submodule.add_mem _ hm₁ hm₂⟩
    refine ⟨LinearMap.ker_eq_bot.1 (LinearMap.ker_eq_bot'.2 ?_), ?_⟩
    · intro u hu
      choose w hw using fun i : Fin k =>
        surjective_stalk_transition F y (Nat.zero_le (n + 1))
          (((modulesStalkFunctor S.U.toScheme y).map (C := S.U.toScheme.Modules)
            (biproduct.π (fun _ : Fin k => F.obj.obj (op 0)) i)).hom u)
      choose z hz using fun i : Fin k => hπsurj (w i)
      have hmf := stalk_idealPowerDesc_apply (F.obj.obj (op (n + 1))) (n + 1) hbot hb e he y w
      rw [show (fun i => ((modulesStalkFunctor S.U.toScheme y).map (C := S.U.toScheme.Modules)
            (F.obj.map (homOfLE (Nat.zero_le (n + 1))).op)).hom (w i)) =
          (fun i => ((modulesStalkFunctor S.U.toScheme y).map (C := S.U.toScheme.Modules)
            (biproduct.π (fun _ : Fin k => F.obj.obj (op 0)) i)).hom u) from funext hw,
        stalkOfTuple_stalk_π, hu, map_zero] at hmf
      have hzero : πL (∑ i, ((r i : B.R)) • z i) = 0 := by
        rw [hπcomb, show (∑ i, germOfBase S y (B.φ ((r i : B.R))) • πL (z i)) =
            ∑ i, (S.U.toScheme.presheaf.germ ⊤ y trivial).hom
              (scalarMap S (B.φ ((r i : B.R)))) • w i from
          Finset.sum_congr rfl fun i _ => by rw [hz i, hgerm i]]
        exact hmf.symm
      have hmem : (∑ i, ((r i : B.R)) • z i) ∈
          (IsLocalRing.maximalIdeal B.R).map
              (algebraMap B.R (completedLocalRing (idealOnOpen S) y)) ^ (n + 1 + 1) •
            (⊤ : Submodule (completedLocalRing (idealOnOpen S) y)
              (completedStalk (idealOnOpen S) F y)) := by
        rw [hJeq]
        exact (hπker _).1 hzero
      have hzmem := fun i => Stacks.Flatness.mem_smul_top_of_sum_smul_mem
        (IsLocalRing.maximalIdeal B.R) (completedStalk (idealOnOpen S) F y)
        (completedLocalRing (idealOnOpen S) y) (n + 1) e₀ r hr z hmem i
      have hzmem' : ∀ i, z i ∈ IdealSheafData.stalk (idealOnOpen S) y •
          (⊤ : Submodule (S.U.toScheme.presheaf.stalk y)
            (completedStalk (idealOnOpen S) F y)) := by
        intro i
        have h0 : z i ∈ completedLocalIdeal (idealOnOpen S) y ^ 1 •
            (⊤ : Submodule (completedLocalRing (idealOnOpen S) y)
              (completedStalk (idealOnOpen S) F y)) := by
          rw [pow_one, ← hJeq]
          exact hzmem i
        have h1 : z i ∈ IdealSheafData.stalk (idealOnOpen S) y ^ 1 •
            (⊤ : Submodule (S.U.toScheme.presheaf.stalk y)
              (completedStalk (idealOnOpen S) F y)) := by
          rw [← restrictScalars_completedLocalIdeal_pow_smul_top (idealOnOpen S) y
            (completedStalk (idealOnOpen S) F y) 1]
          exact h0
        rw [pow_one] at h1
        exact h1
      have hzerou : ∀ i, ((modulesStalkFunctor S.U.toScheme y).map (C := S.U.toScheme.Modules)
          (biproduct.π (fun _ : Fin k => F.obj.obj (op 0)) i)).hom u = 0 := by
        intro i
        rw [← hw i]
        refine (LinearMap.mem_ker (f := ((modulesStalkFunctor S.U.toScheme y).map
          (C := S.U.toScheme.Modules)
          (F.obj.map (homOfLE (Nat.zero_le (n + 1))).op)).hom)).1 ?_
        rw [ker_stalk_transition_zero F y (n + 1), ← hz i]
        exact hπsmulmem _ _ (hzmem' i)
      rw [← stalkOfTuple_stalk_π y (F.obj.obj (op 0)) u, stalkOfTuple]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [hzerou i, map_zero]
    · intro ξ
      have hξ : ((modulesStalkFunctor S.U.toScheme y).map (C := S.U.toScheme.Modules)
          (idealPowerSub S F n).ι).hom ξ ∈
          IdealSheafData.stalk (idealOnOpen S) y ^ (n + 1) •
            (⊤ : Submodule (S.U.toScheme.presheaf.stalk y)
              ((modulesStalkFunctor S.U.toScheme y).obj (F.obj.obj (op (n + 1))))) := by
        rw [← hiyrange]
        exact ⟨ξ, rfl⟩
      obtain ⟨uu, huu, huumem⟩ := hπpre _ _ hξ
      have h1 : uu ∈ (completedLocalIdeal (idealOnOpen S) y ^ (n + 1) •
          (⊤ : Submodule (completedLocalRing (idealOnOpen S) y)
            (completedStalk (idealOnOpen S) F y))).restrictScalars
              (S.U.toScheme.presheaf.stalk y) := by
        rw [restrictScalars_completedLocalIdeal_pow_smul_top (idealOnOpen S) y
          (completedStalk (idealOnOpen S) F y) (n + 1)]
        exact huumem
      have huumem' : uu ∈ (IsLocalRing.maximalIdeal B.R).map
            (algebraMap B.R (completedLocalRing (idealOnOpen S) y)) ^ (n + 1) •
          (⊤ : Submodule (completedLocalRing (idealOnOpen S) y)
            (completedStalk (idealOnOpen S) F y)) := by
        rw [hJeq]
        exact h1
      obtain ⟨z, hzsub⟩ := Stacks.Flatness.exists_sum_smul_sub_mem
        (IsLocalRing.maximalIdeal B.R) (completedStalk (idealOnOpen S) F y)
        (completedLocalRing (idealOnOpen S) y) (n + 1) e₀ r hr huumem'
      rw [hJeq] at hzsub
      have hsub0 : πL (uu - ∑ i, ((r i : B.R)) • z i) = 0 := (hπker _).2 hzsub
      have hπusum : πL uu = ∑ i, germOfBase S y (B.φ ((r i : B.R))) • πL (z i) := by
        have h : πL uu - πL (∑ i, ((r i : B.R)) • z i) = 0 := by
          rw [← map_sub]
          exact hsub0
        rw [← hπcomb]
        exact sub_eq_zero.1 h
      refine ⟨stalkOfTuple y (F.obj.obj (op 0))
        (fun i => ((modulesStalkFunctor S.U.toScheme y).map (C := S.U.toScheme.Modules)
          (F.obj.map (homOfLE (Nat.zero_le (n + 1))).op)).hom (πL (z i))), ?_⟩
      refine hiyinj ?_
      rw [stalk_idealPowerDesc_apply (F.obj.obj (op (n + 1))) (n + 1) hbot hb e he y
        (fun i => πL (z i))]
      refine Eq.trans ?_ huu
      rw [hπusum]
      exact Finset.sum_congr rfl fun i _ => by rw [hgerm i]
  · have hzeroM : ∀ wm : (modulesStalkFunctor S.U.toScheme y).obj (F.obj.obj (op (n + 1))),
        wm = 0 := fun wm => eq_zero_stalk_of_notMem_support F hy (n + 1) wm
    have hzero0 : ∀ v : (modulesStalkFunctor S.U.toScheme y).obj (F.obj.obj (op 0)), v = 0 :=
      fun v => eq_zero_stalk_of_notMem_support F hy 0 v
    have hzeroSub : ∀ ξ : (modulesStalkFunctor S.U.toScheme y).obj
        ((idealPowerSub S F n).toSheafOfModules), ξ = 0 := by
      intro ξ
      refine hiyinj ?_
      rw [map_zero]
      exact hzeroM _
    refine ⟨fun u₁ u₂ _ => ?_, fun ξ => ⟨0, ?_⟩⟩
    · rw [← stalkOfTuple_stalk_π y (F.obj.obj (op 0)) u₁,
        ← stalkOfTuple_stalk_π y (F.obj.obj (op 0)) u₂]
      exact congrArg (stalkOfTuple y (F.obj.obj (op 0)))
        (funext fun i => (hzero0 _).trans (hzero0 _).symm)
    · rw [map_zero, hzeroSub ξ]

/-! ### The decomposition -/

/-- **The direct-sum decomposition of `Iⁿ⁺¹ F_(n+2)`, with its components named.** In the
situation of Stacks 0EJU, for any identification `e` of `F_(n+2)/I F_(n+2)` with `F_1` compatible
with the transition, there are elements `r₁, …, r_k ∈ 𝔪ⁿ⁺¹` (representatives of a `κ`-basis of
`𝔪ⁿ⁺¹/𝔪ⁿ⁺²`) for which `Stacks.Algebraization.idealPowerDesc`, the morphism
`⨁_{i<k} F_1 ⟶ Iⁿ⁺¹ F_(n+1)` whose `i`-th component is multiplication by the image of `rᵢ`, is an
isomorphism.

`Stacks.Algebraization.exists_isoDirectSum_idealPowerSub` forgets the morphism; the form here keeps
it, which is what a computation with the components needs. -/
theorem exists_isIso_idealPowerDesc (B : FlatLocalBase S F) (n : ℕ)
    (e : idealPowerQuotient (idealOnOpen S) 1 (F.obj.obj (op (n + 1))) ≅ F.obj.obj (op 0))
    (he : cokernel.π (C := S.U.toScheme.Modules)
        (idealPowerMultiple (idealOnOpen S) 1 (F.obj.obj (op (n + 1)))).ι ≫ e.hom =
      F.obj.map (homOfLE (Nat.zero_le (n + 1))).op) :
    ∃ (k : ℕ) (r : Fin k → B.R) (_ : ∀ i, r i ∈ IsLocalRing.maximalIdeal B.R ^ (n + 1))
      (hb : ∀ i, RestrictMemIdealPow (idealOnOpen S) (n + 1) (scalarMap S (B.φ (r i)))),
      haveI := F.property.isQuasicoherent (n + 1)
      IsIso (idealPowerDesc (F.obj.obj (op (n + 1))) (n + 1)
        (F.property.idealPowerMultiple_eq_bot (n + 1)) hb e) := by
  classical
  have hqc : (F.obj.obj (op (n + 1))).IsQuasicoherent := F.property.isQuasicoherent (n + 1)
  obtain ⟨k, ⟨e₀⟩⟩ := Stacks.Flatness.exists_pi_linearEquiv_gradedPiece
    (IsLocalRing.maximalIdeal B.R) (n + 1)
  choose r hr using fun i : Fin k =>
    Submodule.Quotient.mk_surjective
      (IsLocalRing.maximalIdeal B.R •
        (⊤ : Submodule B.R ↥(IsLocalRing.maximalIdeal B.R ^ (n + 1))))
      (e₀.symm (Pi.single i (1 : B.R ⧸ IsLocalRing.maximalIdeal B.R)))
  have ha : ∀ i, B.φ ((r i : B.R)) ∈ S.I ^ (n + 1) := by
    intro i
    rw [B.I_eq, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ (r i).2
  have hb : ∀ i, RestrictMemIdealPow (idealOnOpen S) (n + 1)
      (scalarMap S (B.φ ((r i : B.R)))) := fun i =>
    restrictMemIdealPow_scalarMap S (n + 1) (ha i)
  have hbot : idealPowerMultiple (idealOnOpen S) (n + 1 + 1) (F.obj.obj (op (n + 1))) = ⊥ :=
    F.property.idealPowerMultiple_eq_bot (n + 1)
  refine ⟨k, fun i => (r i : B.R), fun i => (r i).2, hb, ?_⟩
  exact AlgebraicGeometry.isIso_of_forall_modulesStalk _ fun y => by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact bijective_stalk_idealPowerDesc S F B n e₀ r (fun i => (hr i).symm) hb hbot e he y

/-- **The direct-sum decomposition of `Iⁿ F_(n+1)` in the proof of Stacks 0EJU.** In the situation
of Stacks 0EJU — a Noetherian local ring `(R, 𝔪)` and a map `R → A` with `I = 𝔪 A` over which the
formal stalks of `(F_n)` along `U ∩ Y` are flat — the subsheaf `Iⁿ⁺¹ F_(n+2)` is isomorphic to a
finite direct sum of copies of `F_1`, the number of copies being `dim_κ 𝔪ⁿ⁺¹/𝔪ⁿ⁺²`.

This is the hypothesis `hdec` of `Stacks.Algebraization.canonicallyExtends_of_isoDirectSum`,
discharged. The isomorphism is `Stacks.Algebraization.idealPowerDesc` for the global functions on
`U` determined by representatives of a `κ`-basis of `𝔪ⁿ⁺¹/𝔪ⁿ⁺²`; that it is one is checked on
stalks (`Stacks.Algebraization.exists_isIso_idealPowerDesc`). -/
theorem exists_isoDirectSum_idealPowerSub (B : FlatLocalBase S F) (n : ℕ) :
    ∃ k : ℕ, Nonempty ((⨁ fun _ : Fin k => F.obj.obj (op 0)) ≅
      (idealPowerSub S F n).toSheafOfModules) := by
  obtain ⟨e, he⟩ := exists_quotientZeroIso F (n + 1)
  obtain ⟨k, r, -, hb, hiso⟩ := exists_isIso_idealPowerDesc S F B n e he
  have hqc : (F.obj.obj (op (n + 1))).IsQuasicoherent := F.property.isQuasicoherent (n + 1)
  exact ⟨k, ⟨asIso (idealPowerDesc (F.obj.obj (op (n + 1))) (n + 1)
    (F.property.idealPowerMultiple_eq_bot (n + 1)) hb e)⟩⟩

/-- **The finiteness step of the proof of Stacks 0EJU.** Under hypotheses (1) and (2) of Stacks
0EJU, bundled as `Stacks.Algebraization.FlatLocalBase`, every
`H⁰(U, Iⁿ F_(n+1))` is a finite `A`-module as soon as `H⁰(U, F_1)` is one.

The source gets this from the direct-sum decomposition of `Iⁿ F_(n+1)` into copies of `F_1`,
which is `Stacks.Algebraization.exists_isoDirectSum_idealPowerSub` above. -/
theorem finite_idealPowerSections_of_flatLocalBase (B : FlatLocalBase S F)
    (h0 : Module.Finite S.A ((globalSectionsSystem S F).obj (op 0))) :
    ∀ n, Module.Finite S.A (idealPowerSections S F n) :=
  finite_idealPowerSections_of_isoDirectSum S F h0
    fun m => exists_isoDirectSum_idealPowerSub S F B m

end Stacks.Algebraization

end
