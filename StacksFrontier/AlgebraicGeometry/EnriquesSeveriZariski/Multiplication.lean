module

public import StacksFrontier.AlgebraicGeometry.AmpleTheory.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleWire.UnitStalk
public import StacksFrontier.AlgebraicGeometry.Modules.InvertibleStalkFree
public import StacksFrontier.AlgebraicGeometry.Modules.StalkSupport
public import StacksFrontier.AlgebraicGeometry.Modules.TensorStalkNaturality
public import StacksFrontier.AlgebraicGeometry.NonvanishingSpelling.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorCanonicalSection
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.VanishingSectionNakayama

/-!
# Multiplication by a global section of a tensor power

Let `X` be a scheme, `L` an invertible `𝒪_X`-module, `σ` a global section of the tensor power
`L ^⊗ e` for some `e : ℕ`, and `F` an arbitrary `𝒪_X`-module. Multiplication by `σ` is a
morphism of `𝒪_X`-modules

`F ⊗ L ^⊗ n ⟶ F ⊗ L ^⊗ (n + e)`,

one for every integer `n`. This file builds that morphism and computes it on the stalk at a
point, which is where the two facts an Enriques--Severi--Zariski argument needs come from:

* at a point of the nonvanishing open `X_σ` the stalk map is **bijective**, in particular
  injective -- `σ` trivialises `L ^⊗ e` there, and tensoring a bijection of stalks with `F_y`
  keeps it bijective;
* at a point off `X_σ` the **whole image** of the stalk map lies in `𝔪_y · (F ⊗ L ^⊗ (n+e))_y`
  -- the germ of `σ` lies in `𝔪_y · (L ^⊗ e)_y` by the definition of vanishing, and an
  elementary tensor whose second factor lies in `I · ⊤` lies in `I · ⊤`.

## The construction

`mulSection` is `F` tensored on the left with `mulSectionPow`, and `mulSectionPow` is the
composite the source describes,

`L ^⊗ n ≅ L ^⊗ n ⊗ 𝒪_X --(1 ⊗ σ)--> L ^⊗ n ⊗ L ^⊗ e ≅ L ^⊗ (n + e)`,

in which `σ` is read as the morphism `𝒪_X ⟶ L ^⊗ e` it induces
(`AlgebraicGeometry.SheafOfModules.unitHomEquiv`), the first isomorphism is the right unit
constraint of the tensor product of sheaves of modules
(`Stacks.SheafOfModules.Invertible.tensorProductRightUnitor`) and the last is the addition law
for the tensor powers of Stacks Tag 01CU (`Stacks.Ample.tensorPowModuleAddIso`). Neither
structural isomorphism is ever evaluated: only the fact that each is an isomorphism is used, and
that enters through `bijective_stalkLinearMap_of_inverse` and through linearity of a stalk map.

## Main definitions

* `Stacks.EnriquesSeveriZariski.twist`: the twist `F ⊗ L ^⊗ n`.
* `Stacks.EnriquesSeveriZariski.sectionHom`: a global section of `M`, read as the morphism
  `𝒪_X ⟶ M` of multiplication by it.
* `Stacks.EnriquesSeveriZariski.mulSectionPow`: multiplication by `σ` on the tensor powers
  themselves, `L ^⊗ n ⟶ L ^⊗ (n + e)`.
* `Stacks.EnriquesSeveriZariski.mulSection`: **multiplication by `σ` on a twist**,
  `F ⊗ L ^⊗ n ⟶ F ⊗ L ^⊗ (n + e)`.

## Main results

* `Stacks.EnriquesSeveriZariski.tensorStalkEquiv_tensorLeftMap`: **naturality of Stacks Tag 01CB
  in the right factor.** The identification of the stalk of a tensor product with the tensor
  product of the stalks carries the stalk map of `1 ⊗ g` to `LinearMap.lTensor` of the stalk map
  of `g`.
* `Stacks.EnriquesSeveriZariski.stalkLinearMap_sectionHom`: **the stalk map of multiplication by
  a global section is multiplication by its germ**, the source stalk being identified with the
  local ring by `Stacks.Ample.unitStalkEquiv`.
* `Stacks.EnriquesSeveriZariski.isStalkBasis_Γgerm_of_mem_nonvanishingLocus`: a global section of
  an invertible module is a stalk basis at every point of its nonvanishing locus.
* `Stacks.EnriquesSeveriZariski.bijective_stalkLinearMap_mulSectionPow` and
  `Stacks.EnriquesSeveriZariski.mem_maximalSmul_stalkLinearMap_mulSectionPow`: the two stalk
  facts for `mulSectionPow`.
* `Stacks.EnriquesSeveriZariski.injective_stalkLinearMap_mulSection`: **where `σ` does not
  vanish, multiplication by `σ` is injective on stalks.**
* `Stacks.EnriquesSeveriZariski.range_stalkLinearMap_mulSection_le`: **where `σ` vanishes, the
  image of multiplication by `σ` on the stalk lies in the maximal ideal times the stalk.**

## Implementation notes

**Which way the morphism is tensored.** `AlgebraicGeometry.Scheme.Modules.tensorRightMap` and
its stalk naturality `AlgebraicGeometry.tensorStalkEquiv_tensorRightMap` tensor a morphism on
the left of a fixed module, `A ⊗ G ⟶ B ⊗ G`; the twist `F ⊗ L ^⊗ n` keeps `F` fixed and moves
the *second* factor, so what is needed is the mirror image. That is
`AlgebraicGeometry.Scheme.Modules.tensorLeftMap`, in
`StacksFrontier/AlgebraicGeometry/Divisors/TensorCanonicalSection.lean`, and it is imported here;
what this file adds is its stalk naturality, the mirror of the existing proof. The braiding is
not used, so no formula for it is needed.

**Isomorphisms are consumed as pairs of mutually inverse morphisms, not through `IsIso`.** The
structural isomorphisms above are stated at the `SheafOfModules (structureSheaf X.presheaf _)`
spelling of `X.Modules`, which is `X.Modules` by `rfl` but is a syntactically different
category instance, and `CategoryTheory.Iso.isIso_hom` is therefore not *found* for them by
instance search: it fails with `failed to synthesize IsIso ...`. So
`AlgebraicGeometry.bijective_stalkLinearMap`, which takes `[IsIso f]`, cannot be used, and
`bijective_stalkLinearMap_of_inverse` takes `hom_inv_id` and `inv_hom_id` as plain hypotheses
instead; those are accepted across the spelling gap by `exact`, which checks at default
transparency.

**The source of `sectionHom` is the stalk that had to be identified.** The stalk map of
`𝒪_X ⟶ M` goes out of the stalk of `𝒪_X` *as a module over itself*, a colimit in `Ab`, whereas
"multiplication by the germ of `σ`" is indexed by the stalk `𝒪_{X,y}`, a colimit in
`CommRingCat`. `Stacks.Ample.unitStalkEquiv` is the comparison, and
`stalkLinearMap_sectionHom` is the only place it is needed: with it, bijectivity of the stalk
map of `sectionHom` is exactly the stalk-basis property of the germ of `σ`.

## References

* [Stacks Project, Tag 0FD7](https://stacks.math.columbia.edu/tag/0FD7)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

open scoped TensorProduct

universe u

namespace Stacks.EnriquesSeveriZariski

/-! ### Tensor products of linear maps -/

section Algebra

variable {R : Type*} [CommRing R] {M N P : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

/-- Tensoring on the left by `M` carries a linear map whose image lies in `I · ⊤` to a linear map
whose image lies in `I · ⊤`. This is
`Stacks.SheafOfModules.map_mem_smul_top_of_range_le` at `LinearMap.id` in the first factor,
`LinearMap.lTensor` being `TensorProduct.map LinearMap.id` by definition. -/
theorem lTensor_mem_ideal_smul_top (I : Ideal R) (g : N →ₗ[R] P)
    (hg : ∀ b, g b ∈ I • (⊤ : Submodule R P)) (z : M ⊗[R] N) :
    LinearMap.lTensor M g z ∈ I • (⊤ : Submodule R (M ⊗[R] P)) :=
  Stacks.SheafOfModules.map_mem_smul_top_of_range_le I LinearMap.id g hg z

/-- Tensoring on the left by `M` carries a bijective linear map to a bijective linear map: the
map is the underlying map of `LinearEquiv.lTensor`. -/
theorem bijective_lTensor (g : N →ₗ[R] P) (hg : Function.Bijective g) :
    Function.Bijective (LinearMap.lTensor M g) :=
  (LinearEquiv.lTensor M (LinearEquiv.ofBijective g hg)).bijective

end Algebra

/-- A map that agrees pointwise with a composite of bijections is bijective. -/
private theorem bijective_of_forall_eq_comp {α β γ : Type*} {f : α → γ} {g : β → γ} {h : α → β}
    (hg : Function.Bijective g) (hh : Function.Bijective h) (e : ∀ z, f z = g (h z)) :
    Function.Bijective f := by
  rw [funext e]
  exact hg.comp hh

variable {X : Scheme.{u}}

/-! ### Tensoring a morphism on the left -/

/-- Tensoring on the left by `F` sends the image of a pure tensor of local sections to the image
of the pure tensor whose second factor has been pushed forward. -/
theorem stalkLinearMap_tensorLeftMap_tensorSheafGerm (F : X.Modules) {A B : X.Modules}
    (g : A ⟶ B) (x : X) (U : X.Opens) (hx : x ∈ U) (m : F.val.obj (op U))
    (a : A.val.obj (op U)) :
    stalkLinearMap _ _ (Scheme.Modules.tensorLeftMap F g) x
        (PresheafOfModules.tensorSheafGerm X.sheaf F A x U hx m a) =
      PresheafOfModules.tensorSheafGerm X.sheaf F B x U hx m (g.val.app (op U) a) :=
  (stalkLinearMap_germ (Scheme.Modules.tensorObj F A) (Scheme.Modules.tensorObj F B)
      (Scheme.Modules.tensorLeftMap F g) U x hx _).trans
    (congrArg (ConcreteCategory.hom ((Scheme.Modules.tensorObj F B).presheaf.germ U x hx))
      ((PresheafOfModules.unit_naturality_apply
            (α := 𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj)
            (PresheafOfModules.tensorHom (𝟙 F.val) g.val) (op U)
            (m ⊗ₜ[X.sheaf.obj.obj (op U)] a)).trans
        (congrArg (ConcreteCategory.hom (PresheafOfModules.Hom.app
            ((PresheafOfModules.sheafificationAdjunction
                (R := Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)
                (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj)).unit.app
              (PresheafOfModules.tensorObj F.val B.val)) (op U)))
          (PresheafOfModules.tensorHom_tmul (𝟙 F.val) g.val (op U) m a))))

/-- **Naturality of Stacks Tag 01CB in the right factor.** The identification of the stalk of
`F ⊗_{𝒪_X} A` with `F_x ⊗_{𝒪_{X,x}} A_x` carries the stalk map of `1 ⊗ g` to the left tensor
product of `F_x` with the stalk map of `g`. -/
theorem tensorStalkEquiv_tensorLeftMap (F : X.Modules) {A B : X.Modules} (g : A ⟶ B) (x : X)
    (z : (Scheme.Modules.tensorObj F A).presheaf.stalk x) :
    tensorStalkEquiv F B x (stalkLinearMap _ _ (Scheme.Modules.tensorLeftMap F g) x z) =
      LinearMap.lTensor (F.presheaf.stalk x) (stalkLinearMap A B g x)
        (tensorStalkEquiv F A x z) := by
  obtain ⟨w, rfl⟩ : ∃ w, (tensorStalkEquiv F A x).symm w = z :=
    ⟨tensorStalkEquiv F A x z, (tensorStalkEquiv F A x).symm_apply_apply z⟩
  rw [LinearEquiv.apply_symm_apply]
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, map_add, map_add, hc, hd]
  | tmul p q =>
      obtain ⟨U, hxU, m, hm⟩ := F.presheaf.exists_germ_eq p
      obtain ⟨V, hxV, a, ha⟩ := A.presheaf.exists_germ_eq q
      have hxW : x ∈ U ⊓ V := ⟨hxU, hxV⟩
      let m' : F.val.obj (op (U ⊓ V)) :=
        F.val.map (homOfLE (inf_le_left (a := U) (b := V))).op m
      let a' : A.val.obj (op (U ⊓ V)) :=
        A.val.map (homOfLE (inf_le_right (a := U) (b := V))).op a
      have hpm : F.presheaf.germ (U ⊓ V) x hxW m' = p :=
        (F.presheaf.germ_res_apply _ x hxW m).trans hm
      have hqa : A.presheaf.germ (U ⊓ V) x hxW a' = q :=
        (A.presheaf.germ_res_apply _ x hxW a).trans ha
      have key : (tensorStalkEquiv F A x).symm (p ⊗ₜ q) =
          PresheafOfModules.tensorSheafGerm X.sheaf F A x (U ⊓ V) hxW m' a' :=
        (tensorStalkEquiv F A x).injective
          (by rw [LinearEquiv.apply_symm_apply, tensorStalkEquiv_germ, hpm, hqa])
      rw [key, stalkLinearMap_tensorLeftMap_tensorSheafGerm, tensorStalkEquiv_germ,
        LinearMap.lTensor_tmul, ← hpm, ← hqa]
      exact congrArg (fun y => F.presheaf.germ (U ⊓ V) x hxW m' ⊗ₜ[X.presheaf.stalk x] y)
        (stalkLinearMap_germ A B g (U ⊓ V) x hxW a').symm

/-- **A bijective stalk map stays bijective after tensoring on the left.** -/
theorem bijective_stalkLinearMap_tensorLeftMap (F : X.Modules) {A B : X.Modules} (g : A ⟶ B)
    (x : X) (hg : Function.Bijective (stalkLinearMap A B g x)) :
    Function.Bijective (stalkLinearMap _ _ (Scheme.Modules.tensorLeftMap F g) x) := by
  refine bijective_of_forall_eq_comp
    (((tensorStalkEquiv F B x).symm.bijective).comp (bijective_lTensor _ hg))
    (tensorStalkEquiv F A x).bijective fun z => ?_
  rw [Function.comp_apply, ← tensorStalkEquiv_tensorLeftMap, LinearEquiv.symm_apply_apply]

/-- A bijective stalk map stays injective after tensoring on the left; this is the half the
injectivity statement for a twist consumes. -/
theorem injective_stalkLinearMap_tensorLeftMap (F : X.Modules) {A B : X.Modules} (g : A ⟶ B)
    (x : X) (hg : Function.Bijective (stalkLinearMap A B g x)) :
    Function.Injective (stalkLinearMap _ _ (Scheme.Modules.tensorLeftMap F g) x) :=
  (bijective_stalkLinearMap_tensorLeftMap F g x hg).injective

/-- **A stalk map whose image lies in `𝔪_x · B_x` still has its image inside `𝔪_x · (F ⊗ B)_x`
after tensoring on the left.** Nothing is asked of `F`: an elementary tensor whose second factor
lies in `𝔪_x · B_x` lies in `𝔪_x · (F_x ⊗ B_x)`. -/
theorem mem_maximalSmul_stalkLinearMap_tensorLeftMap (F : X.Modules) {A B : X.Modules}
    (g : A ⟶ B) (x : X)
    (hg : ∀ w, stalkLinearMap A B g x w ∈ Stacks.ModuleStalk.maximalSmul B x)
    (z : (Scheme.Modules.tensorObj F A).presheaf.stalk x) :
    stalkLinearMap _ _ (Scheme.Modules.tensorLeftMap F g) x z ∈
      Stacks.ModuleStalk.maximalSmul (Scheme.Modules.tensorObj F B) x := by
  have h1 : LinearMap.lTensor (F.presheaf.stalk x) (stalkLinearMap A B g x)
      (tensorStalkEquiv F A x z) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) •
        (⊤ : Submodule (X.presheaf.stalk x) (F.presheaf.stalk x ⊗[X.presheaf.stalk x]
          B.presheaf.stalk x)) :=
    lTensor_mem_ideal_smul_top _ _ hg _
  have h2 := Stacks.SheafOfModules.map_mem_ideal_smul_top
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (tensorStalkEquiv F B x).symm.toLinearMap h1
  rw [← tensorStalkEquiv_tensorLeftMap F g x z] at h2
  have h3 : stalkLinearMap _ _ (Scheme.Modules.tensorLeftMap F g) x z ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) •
        (⊤ : Submodule (X.presheaf.stalk x)
          ((Scheme.Modules.tensorObj F B).presheaf.stalk x)) := by
    simpa using h2
  exact h3

/-! ### Composites -/

/-- The stalk map of a left inverse `v` of `u` undoes the stalk map of `u`. -/
private theorem stalkLinearMap_apply_of_comp_eq_id {A B : X.Modules} (u : A ⟶ B) (v : B ⟶ A)
    (h : u ≫ v = 𝟙 A) (x : X) (w : A.presheaf.stalk x) :
    stalkLinearMap B A v x (stalkLinearMap A B u x w) = w :=
  (Scheme.Modules.stalkLinearMap_comp u v x w).symm.trans
    ((congrArg (fun k : A ⟶ A => stalkLinearMap A A k x w) h).trans
      (Scheme.Modules.stalkLinearMap_id A x w))

/-- The stalk map of a morphism with a two-sided inverse is bijective. This replaces
`AlgebraicGeometry.bijective_stalkLinearMap` for the structural isomorphisms used below, whose
`IsIso` instance is not found by instance search; see the implementation notes. -/
theorem bijective_stalkLinearMap_of_inverse {A B : X.Modules} (u : A ⟶ B) (v : B ⟶ A)
    (h1 : u ≫ v = 𝟙 A) (h2 : v ≫ u = 𝟙 B) (x : X) :
    Function.Bijective (stalkLinearMap A B u x) := by
  exact ⟨fun z z' hz => by
    rw [← stalkLinearMap_apply_of_comp_eq_id u v h1 x z, ← stalkLinearMap_apply_of_comp_eq_id u v h1
      x z', hz], fun w => ⟨_, stalkLinearMap_apply_of_comp_eq_id v u h2 x w⟩⟩

/-- A composite of morphisms whose stalk maps are bijective has bijective stalk map. -/
theorem bijective_stalkLinearMap_comp {A B C : X.Modules} (u : A ⟶ B) (v : B ⟶ C) (x : X)
    (hu : Function.Bijective (stalkLinearMap A B u x))
    (hv : Function.Bijective (stalkLinearMap B C v x)) :
    Function.Bijective (stalkLinearMap A C (u ≫ v) x) := by
  exact bijective_of_forall_eq_comp hv hu (Scheme.Modules.stalkLinearMap_comp u v x)

/-- If the stalk map of `u` has its image inside `𝔪_x · B_x`, so does the stalk map of `u ≫ v`:
a linear map carries `𝔪_x · ⊤` into `𝔪_x · ⊤`. -/
theorem mem_maximalSmul_stalkLinearMap_comp_left {A B C : X.Modules} (u : A ⟶ B) (v : B ⟶ C)
    (x : X) (hu : ∀ w, stalkLinearMap A B u x w ∈ Stacks.ModuleStalk.maximalSmul B x)
    (z : A.presheaf.stalk x) :
    stalkLinearMap A C (u ≫ v) x z ∈ Stacks.ModuleStalk.maximalSmul C x := by
  rw [Scheme.Modules.stalkLinearMap_comp]
  exact Stacks.SheafOfModules.map_mem_ideal_smul_top _ (stalkLinearMap B C v x) (hu z)

/-- If the stalk map of `v` has its image inside `𝔪_x · C_x`, so does the stalk map of
`u ≫ v`. -/
theorem mem_maximalSmul_stalkLinearMap_comp_right {A B C : X.Modules} (u : A ⟶ B) (v : B ⟶ C)
    (x : X) (hv : ∀ w, stalkLinearMap B C v x w ∈ Stacks.ModuleStalk.maximalSmul C x)
    (z : A.presheaf.stalk x) :
    stalkLinearMap A C (u ≫ v) x z ∈ Stacks.ModuleStalk.maximalSmul C x := by
  rw [Scheme.Modules.stalkLinearMap_comp]
  exact hv _

/-! ### Multiplication by a global section -/

/-- **A global section of `M`, read as the morphism `𝒪_X ⟶ M` of multiplication by it.** This is
`AlgebraicGeometry.SheafOfModules.unitHomEquiv` run backwards, with the restriction-compatible
family named by the global section supplied by
`Stacks.NonvanishingSpelling.sectionsEquiv`. -/
def sectionHom (M : X.Modules) (σ : Γ(M, ⊤)) : Stacks.Ample.unitModule X ⟶ M :=
  M.unitHomEquiv.symm ((Stacks.NonvanishingSpelling.sectionsEquiv X M).symm σ)

/-- **The stalk map of multiplication by a global section is multiplication by its germ.** The
source is the stalk of `𝒪_X` as a module over itself, identified with the local ring
`𝒪_{X,y}` by `Stacks.Ample.unitStalkEquiv`; through that identification the stalk map is
`r ↦ r • germ_y σ`. -/
theorem stalkLinearMap_sectionHom (M : X.Modules) (σ : Γ(M, ⊤)) (y : X)
    (z : (Stacks.Ample.unitModule X).presheaf.stalk y) :
    stalkLinearMap _ _ (sectionHom M σ) y z =
      Stacks.Ample.unitStalkEquiv X y z • (M.presheaf.Γgerm y).hom σ := by
  obtain ⟨W, hyW, a, rfl⟩ :=
    TopCat.Presheaf.exists_germ_eq (Stacks.Ample.unitModule X).presheaf z
  have happ : (sectionHom M σ).val.app (op W) a =
      (show Γ(X, W) from a) • M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op σ :=
    Stacks.NonvanishingTrivialize.unitHomEquiv_symm_app (X := X.toRingedSpace)
      ((Stacks.NonvanishingSpelling.sectionsEquiv X M).symm σ) W (show Γ(X, W) from a)
  have hres : (M.presheaf.germ W y hyW).hom (M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op σ) =
      (M.presheaf.Γgerm y).hom σ :=
    M.presheaf.germ_res_apply (homOfLE (le_top : W ≤ ⊤)) y hyW σ
  refine Eq.trans (stalkLinearMap_germ _ M (sectionHom M σ) W y hyW a) ?_
  rw [happ, Stacks.ModuleStalk.germ_smul, hres]
  exact congrArg (fun r : X.presheaf.stalk y => r • (M.presheaf.Γgerm y).hom σ)
    (Stacks.Ample.unitStalkFun_germ X y W hyW a).symm

/-- **A global section of an invertible module is a stalk basis at every point of its
nonvanishing locus.** Pick any stalk basis `b` at `y`; the germ of `σ` is `r • b` for a unique
`r`, and not vanishing at `y` forces `r` to be a unit by
`Stacks.ModuleStalk.smul_mem_maximalSmul_iff`, so `r • b` is again a stalk basis. -/
theorem isStalkBasis_Γgerm_of_mem_nonvanishingLocus (M : X.Modules)
    [Stacks.Ample.IsInvertibleModule X M] (σ : Γ(M, ⊤)) {y : X}
    (hy : y ∈ Stacks.Ample.nonvanishingLocus M σ) :
    Stacks.Divisors.IsStalkBasis M y ((M.presheaf.Γgerm y).hom σ) := by
  obtain ⟨V, hyV, b, hb⟩ := Stacks.InvertibleStalk.exists_germ_isStalkBasis M y
  have hco := hb.smul_coord ((M.presheaf.Γgerm y).hom σ)
  rw [Stacks.Ample.mem_nonvanishingLocus_iff, ← hco] at hy
  rw [← hco]
  have h := (Stacks.ModuleStalk.smul_mem_maximalSmul_iff
    (hb.coord ((M.presheaf.Γgerm y).hom σ)) _).not.mp hy
  rw [not_or, not_not] at h
  exact hb.smul_of_isUnit h.1

/-- **Clause 2 of Stacks Tag 01CY on the stalk at a nonvanishing point.** Multiplication by a
global section of an invertible module is bijective on the stalk at every point of its
nonvanishing locus: it is multiplication by a stalk basis, read through the identification of
the stalk of `𝒪_X` with the local ring. -/
theorem bijective_stalkLinearMap_sectionHom (M : X.Modules)
    [Stacks.Ample.IsInvertibleModule X M] (σ : Γ(M, ⊤)) {y : X}
    (hy : y ∈ Stacks.Ample.nonvanishingLocus M σ) :
    Function.Bijective (stalkLinearMap _ _ (sectionHom M σ) y) := by
  exact bijective_of_forall_eq_comp (isStalkBasis_Γgerm_of_mem_nonvanishingLocus M σ hy)
    (Stacks.Ample.unitStalkEquiv X y).bijective (stalkLinearMap_sectionHom M σ y)

/-- **At a vanishing point the image of multiplication by the section lies in `𝔪_y · M_y`.**
Vanishing at `y` says exactly that the germ of `σ` lies there, and `𝔪_y · M_y` is a
submodule. -/
theorem mem_maximalSmul_stalkLinearMap_sectionHom (M : X.Modules) (σ : Γ(M, ⊤)) {y : X}
    (hy : y ∉ Stacks.Ample.nonvanishingLocus M σ)
    (z : (Stacks.Ample.unitModule X).presheaf.stalk y) :
    stalkLinearMap _ _ (sectionHom M σ) y z ∈ Stacks.ModuleStalk.maximalSmul M y := by
  rw [stalkLinearMap_sectionHom]
  exact Submodule.smul_mem _ _ (not_not.mp hy)

/-! ### Multiplication on the tensor powers -/

variable (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-- **The twist `F ⊗_{𝒪_X} L ^⊗ n`** of an `𝒪_X`-module by an integer tensor power of `L`. -/
abbrev twist (F : X.Modules) (n : ℤ) : X.Modules :=
  Scheme.Modules.tensorObj F (Stacks.Ample.tensorPowModule X L n)

/-- **Multiplication by a global section `σ` of `L ^⊗ e` on the tensor powers of `L`**, as a
morphism `L ^⊗ n ⟶ L ^⊗ (n + e)`. It is the composite of the right unit constraint, of `σ` read
as a morphism out of `𝒪_X` and tensored on the left by `L ^⊗ n`, and of the addition law for the
tensor powers of Stacks Tag 01CU. -/
def mulSectionPow {e : ℕ} (σ : Γ(Stacks.Ample.tensorPowModule X L (e : ℤ), ⊤)) (n : ℤ) :
    Stacks.Ample.tensorPowModule X L n ⟶ Stacks.Ample.tensorPowModule X L (n + e) :=
  (Stacks.SheafOfModules.Invertible.tensorProductRightUnitor X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X)
      (Stacks.Ample.tensorPowModule X L n)).inv ≫
    (Scheme.Modules.tensorLeftMap (Stacks.Ample.tensorPowModule X L n)
        (sectionHom (Stacks.Ample.tensorPowModule X L (e : ℤ)) σ) ≫
      (Stacks.Ample.tensorPowModuleAddIso X L n (e : ℤ)).hom)

/-- **Where `σ` does not vanish, multiplication by `σ` is bijective on the stalk of the tensor
powers.** The two structural morphisms are isomorphisms, and the middle one is bijective on the
stalk because `σ` is. -/
theorem bijective_stalkLinearMap_mulSectionPow {e : ℕ}
    (σ : Γ(Stacks.Ample.tensorPowModule X L (e : ℤ), ⊤)) (n : ℤ) {y : X}
    (hy : y ∈ Stacks.AmpleTheory.powNonvanishingOpen X L e σ) :
    Function.Bijective (stalkLinearMap _ _ (mulSectionPow L σ n) y) :=
  bijective_stalkLinearMap_comp _ _ y
    (bijective_stalkLinearMap_of_inverse _ _ (Iso.inv_hom_id _) (Iso.hom_inv_id _) y)
    (bijective_stalkLinearMap_comp _ _ y
      (bijective_stalkLinearMap_tensorLeftMap _ _ y
        (bijective_stalkLinearMap_sectionHom _ σ hy))
      (bijective_stalkLinearMap_of_inverse _ _ (Iso.hom_inv_id _) (Iso.inv_hom_id _) y))

/-- **Where `σ` vanishes, the image of multiplication by `σ` on the stalk of the tensor powers
lies in `𝔪_y · (L ^⊗ (n+e))_y`.** -/
theorem mem_maximalSmul_stalkLinearMap_mulSectionPow {e : ℕ}
    (σ : Γ(Stacks.Ample.tensorPowModule X L (e : ℤ), ⊤)) (n : ℤ) {y : X}
    (hy : y ∉ Stacks.AmpleTheory.powNonvanishingOpen X L e σ)
    (z : (Stacks.Ample.tensorPowModule X L n).presheaf.stalk y) :
    stalkLinearMap _ _ (mulSectionPow L σ n) y z ∈
      Stacks.ModuleStalk.maximalSmul (Stacks.Ample.tensorPowModule X L (n + e)) y :=
  mem_maximalSmul_stalkLinearMap_comp_right _ _ y
    (fun w => mem_maximalSmul_stalkLinearMap_comp_left _ _ y
      (fun w' => mem_maximalSmul_stalkLinearMap_tensorLeftMap _ _ y
        (fun v => mem_maximalSmul_stalkLinearMap_sectionHom _ σ hy v) w') w) z

/-! ### Multiplication by a global section on a twist -/

/-- **Multiplication by a global section `σ` of `L ^⊗ e`, as a morphism of twists**
`F ⊗ L ^⊗ n ⟶ F ⊗ L ^⊗ (n + e)`: multiplication on the tensor powers, tensored on the left by
`F`. -/
def mulSection {e : ℕ} (σ : Γ(Stacks.Ample.tensorPowModule X L (e : ℤ), ⊤)) (F : X.Modules)
    (n : ℤ) : twist L F n ⟶ twist L F (n + e) :=
  Scheme.Modules.tensorLeftMap F (mulSectionPow L σ n)

/-- **Where `σ` does not vanish, multiplication by `σ` is injective on stalks.** This is clause
2 of Stacks Tag 01CY, whiskered by an arbitrary `F`: multiplication by `σ` is bijective on the
stalk of `L ^⊗ n` at a point of `X_σ`, and tensoring with `F_y` preserves bijectivity. -/
theorem injective_stalkLinearMap_mulSection {e : ℕ}
    (σ : Γ(Stacks.Ample.tensorPowModule X L (e : ℤ), ⊤)) (F : X.Modules) (n : ℤ) {y : X}
    (hy : y ∈ Stacks.AmpleTheory.powNonvanishingOpen X L e σ) :
    Function.Injective (stalkLinearMap _ _ (mulSection L σ F n) y) :=
  injective_stalkLinearMap_tensorLeftMap F _ y
    (bijective_stalkLinearMap_mulSectionPow L σ n hy)

/-- **Where `σ` vanishes, every value of multiplication by `σ` on stalks lies in the maximal
ideal times the stalk.** The germ of `σ` lies in `𝔪_y · (L ^⊗ e)_y`, and an elementary tensor
with such a second factor lies in `𝔪_y` times the tensor product. -/
theorem range_stalkLinearMap_mulSection_le {e : ℕ}
    (σ : Γ(Stacks.Ample.tensorPowModule X L (e : ℤ), ⊤)) (F : X.Modules) (n : ℤ) {y : X}
    (hy : y ∉ Stacks.AmpleTheory.powNonvanishingOpen X L e σ) :
    LinearMap.range (stalkLinearMap _ _ (mulSection L σ F n) y) ≤
      IsLocalRing.maximalIdeal (X.presheaf.stalk y) •
        (⊤ : Submodule (X.presheaf.stalk y) ((twist L F (n + e)).presheaf.stalk y)) := by
  rintro w ⟨z, rfl⟩
  exact mem_maximalSmul_stalkLinearMap_tensorLeftMap F _ y
    (fun v => mem_maximalSmul_stalkLinearMap_mulSectionPow L σ n hy v) z

end Stacks.EnriquesSeveriZariski

end
