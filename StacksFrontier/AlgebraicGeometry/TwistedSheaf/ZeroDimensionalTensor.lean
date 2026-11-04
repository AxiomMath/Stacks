module

public import StacksFrontier.AlgebraicGeometry.Cohomology.GlobalGeneration.ZeroDimensionalSupport
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.HomGlue
public import StacksFrontier.AlgebraicGeometry.NonvanishingTrivialization.Basic
import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.TildeTensorSections
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.BaseCase
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.Dimension

/-!
# An invertible sheaf does not move a coherent sheaf with zero-dimensional support

Let `ℱ` be a coherent sheaf on a locally Noetherian scheme whose support has dimension at most
zero, and let `ℳ` be an invertible sheaf of modules. Then

  `ℱ ⊗_{𝒪_X} ℳ ≅ ℱ`.

This is the statement [Stacks, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT) establishes
at rank one, and it is the hypothesis `hbase` of
`AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_tensorInvertibleIso`
(`StacksFrontier/AlgebraicGeometry/TwistedSheaf/BaseCase.lean`): the base case of the induction
of [Stacks, Tag 0BEM](https://stacks.math.columbia.edu/tag/0BEM). Discharging it leaves Tag
0BEM's first-difference identity `hstep` as that tag's only remaining input, which is what
`AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_hstep` records.

## The construction

The isomorphism is produced as the comparison morphism

  `φ : ℱ ⟶ ℱ ⊗ ℳ`,  `s ↦ s ⊗ a`,

glued out of chartwise data, and then shown to be invertible on every stalk. Neither half needs
anything about the support beyond two facts, both already in the library:

* the support is a *discrete* subspace, so each of its points `x` has an open neighbourhood
  `N_x` meeting the support in `x` alone
  (`AlgebraicGeometry.exists_open_neighborhood_meets_support_singleton`);
* an invertible sheaf has, around each point, a section whose germ is a basis of the stalk
  (`Stacks.SheafOfModules.exists_tensorPairing_eq_unitSection` together with
  `Stacks.SheafOfModules.bijective_smul_germ_of_tensorPairing_eq_unitSection`, the converse half
  of Tag 0B8M).

The covering used is `N_x ⊓ T_x` for `x` in the support — where `T_x` trivializes `ℳ` — together
with the *complement of the support*, over which the chartwise map is `s ↦ s ⊗ 0`. **Every
overlap of two distinct members misses the support**: the complement does by definition, and a
point of `N_x ⊓ N_{x'}` in the support is both `x` and `x'`. The agreement condition of the
glueing is therefore free, because the support of `ℱ ⊗ ℳ` is contained in that of `ℱ` and so
the sections of `ℱ ⊗ ℳ` over such an overlap form a subsingleton. This is the only place
zero-dimensionality of the support enters, and it enters to make a compatibility *vacuous*
rather than to verify it.

On stalks there are two cases. At a point of the support the chart `N_x ⊓ T_x` contains it, and
the stalk map is, read through `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso`, the
  map `g ↦ g ⊗ a_x` with `a_x`
a basis of `ℳ_x`; that is the right unitor `ℱ_x ≅ ℱ_x ⊗ 𝒪_x` followed by a bijection, hence
bijective. Off the support both stalks vanish and every map between them is bijective.

## Main definitions

* `AlgebraicGeometry.tensorModules`: the tensor product of two sheaves of modules on a scheme,
  at the type `AlgebraicGeometry.Scheme.Modules`. Not a new notion — see its docstring.
* `AlgebraicGeometry.tmulSection`: the map `s ↦ s ⊗ a|_V` on sections, for a fixed section `a`
  of the second factor.

## Main results

* `AlgebraicGeometry.notMem_supp_tensorSheaf_of_notMem_supp`: the support of a tensor product is
  contained in the support of either factor.
* `AlgebraicGeometry.exists_hom_app_eq_tmulSection`: the chartwise maps `s ↦ s ⊗ a_i|_V` glue to
  a morphism `ℱ ⟶ ℱ ⊗ ℳ` as soon as two distinct members of the covering meet only outside the
  support of `ℱ`.
* `AlgebraicGeometry.exists_germ_basis_of_isInvertible`: an invertible sheaf has a local basis
  section.
* `AlgebraicGeometry.nonempty_tensorModulesIso_of_topologicalKrullDim_supp_le_zero`: **the
  theorem of this file**, `ℱ ⊗ ℳ ≅ ℱ`.
* `AlgebraicGeometry.tensorInvertibleIso_of_natDimSupp`: the same in the exact shape `hbase` is
  stated in, with the descent measure `AlgebraicGeometry.natDimSupp` of Tag 0BEM.
* `AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_hstep`: **Tag 0BEM from `hstep`
  alone.** Its predecessor
  `AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_natDimSupp` carried two geometric
  hypotheses; this one carries only the first-difference identity.

## Implementation notes

**Three spellings of one tensor product.**
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf`,
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf` and `AlgebraicGeometry.tensorModules`
are the same term; what differs is the declared type of the result, hence which notation and
which instances are available without a conversion. Section-level statements use
`Scheme.Modules`, so that `Γ(-, U)` resolves; stalk-level statements use
`SheafOfModules (structureSheafRing X.toRingedSpace)`, because the module structure on a stalk
(`Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule`) is registered at that spelling and
instance search does not unfold `Scheme.ringCatSheaf` to reach it. The conversions between them
are definitional equalities.

**Why the comparison goes `ℱ ⟶ ℱ ⊗ ℳ` and not the other way.** A map *out of* a sheafified
tensor product is not given by data on sections; a map *into* one is, by
`Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection`. The glueing lemma
`Stacks.AlgebraicGeometry.ModuleLimits.exists_hom_app_eq_of_cover` consumes exactly sectionwise
data, so the comparison is built in this direction and inverted afterwards.

## References

* [Stacks Project, Tag 0BEM](https://stacks.math.columbia.edu/tag/0BEM)
* [Stacks Project, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace TensorProduct

/-- **Tensoring with a basis of a free rank-one module is bijective.** If `c ↦ c • b` is a
bijection `R → B` then `x ↦ x ⊗ b` is a bijection `A → A ⊗[R] B`, being the right unitor
`A ≅ A ⊗[R] R` followed by that bijection in the second factor. -/
theorem bijective_tmul_right {R A B : Type u} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] (b : B) (hb : Function.Bijective fun c : R => c • b) :
    Function.Bijective fun x : A => x ⊗ₜ[R] b := by
  let e : R ≃ₗ[R] B := LinearEquiv.ofBijective (LinearMap.toSpanSingleton R B b) hb
  have he : e 1 = b := one_smul R b
  let Ψ : A ≃ₗ[R] TensorProduct R A B :=
    (TensorProduct.rid R A).symm.trans (TensorProduct.congr (LinearEquiv.refl R A) e)
  have hΨ : ∀ x : A, Ψ x = x ⊗ₜ[R] b := fun x => by
    show TensorProduct.congr (LinearEquiv.refl R A) e ((TensorProduct.rid R A).symm x) = _
    rw [TensorProduct.rid_symm_apply, TensorProduct.congr_tmul, he]
    rfl
  exact (funext hΨ : ⇑Ψ = fun x : A => x ⊗ₜ[R] b) ▸ Ψ.bijective

end TensorProduct

namespace Stacks.SheafOfModules.TensorStalkRingedSpace

variable {X : RingedSpace.{u, u}}

/-! ### Sections of the tensor product -/

/-- Restricting a section twice along inclusions of opens is restricting once. -/
theorem secRestr_secRestr (F : PresheafOfModules.{u} (O X)) {U V W : Opens X.carrier}
    (h₁ : V ≤ W) (h₂ : U ≤ V) (a : F.obj (op W)) :
    ((F).restrictₛₗ ((homOfLE (h₂.trans h₁)).op)) a
      = ((F).restrictₛₗ ((homOfLE h₂).op)) (((F).restrictₛₗ ((homOfLE h₁).op)) a) := by
  show (F.map (homOfLE (h₂.trans h₁)).op).hom a
    = (F.map (homOfLE h₂).op).hom ((F.map (homOfLE h₁).op).hom a)
  rw [← PresheafOfModules.map_comp_apply]
  exact F.congr_map_apply (Subsingleton.elim _ _) a

/-- The canonical map on sections into the sheafified tensor product commutes with restriction:
it is the component of a morphism of presheaves of modules. -/
theorem toTensorSheafSection_map (F H : SheafOfModules.{u} (structureSheafRing X))
    {U V : (Opens X.carrier)ᵒᵖ} (f : U ⟶ V)
    (t : TensorProduct (X.presheaf.obj U) (F.val.obj U) (H.val.obj U)) :
    toTensorSheafSection X F H V
        (((PresheafOfModules.tensorObj (O := (X).presheaf) (F.val) (H.val)).restrictₛₗ
          (f)).toAddMonoidHom t)
      = ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj
          (F)).obj (H))).val.map f (toTensorSheafSection X F H U t) :=
  PresheafOfModules.naturality_apply
    (sheafifyUnit X ((PresheafOfModules.tensorObj (O := (X).presheaf) (F.val) (H.val)))) f t

/-! ### The stalk of the comparison morphism -/

/-- The germ of the restriction of a section to a smaller open is the germ of the section. -/
private theorem grpGerm_restrictₛₗ (M : SheafOfModules.{u} (structureSheafRing X))
    {V W : Opens X.carrier} (h : V ≤ W) (y : X.carrier) (hy : y ∈ V) (a : M.val.obj (op W)) :
    grpGerm X M.val y V hy (((M.val).restrictₛₗ ((homOfLE h).op)) a)
      = grpGerm X M.val y W (h hy) a :=
  TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) M.val.presheaf (homOfLE h) y hy a

/-- **The stalk of `s ↦ s ⊗ a` is `g ↦ g ⊗ a_y`.** If `φ` acts on the sections over every open
inside `W` by tensoring with the fixed section `a` of `M`, then its stalk map at a point `y` of
`W` is, read through `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso`, tensoring with
  the germ of `a` at `y`.

Every element of the stalk is the germ of a section over some neighbourhood, which may be taken
inside `W` after intersecting; there the hypothesis applies and
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso_germ` evaluates the comparison. -/
theorem tensorStalkIso_stalkMapL_eq (G M : SheafOfModules.{u} (structureSheafRing X))
    (φ : G ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj
      (G)).obj (M)))
    (W : Opens X.carrier) (a : M.val.obj (op W))
    (hφ : ∀ (V : Opens X.carrier) (h : V ≤ W) (s : G.val.obj (op V)),
      (φ.val.app (op V)).hom s = toTensorSheafSection X G M (op V)
        (s ⊗ₜ[X.presheaf.obj (op V)] ((M.val).restrictₛₗ ((homOfLE h).op)) a))
    (y : X.carrier) (hy : y ∈ W) (g : grpStalk X G.val y) :
    tensorStalkIso X y G M (stalkMapL X G.val
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj
          (G)).obj (M))).val φ.val y g)
      = g ⊗ₜ[ringStalk X y] grpGerm X M.val y W hy a := by
  obtain ⟨U, hyU, s, hs⟩ := Stacks.SheafOfModules.exists_grpGerm_eq X G.val y g
  have hyV : y ∈ U ⊓ W := ⟨hyU, hy⟩
  have hgs : grpGerm X G.val y (U ⊓ W) hyV
      (((G.val).restrictₛₗ ((homOfLE (inf_le_left : U ⊓ W ≤ U)).op)) s) = g :=
    (grpGerm_restrictₛₗ G (inf_le_left : U ⊓ W ≤ U) y hyV s).trans hs
  rw [← hgs, Stacks.SheafOfModules.stalkMapL_germ X φ.val y (U ⊓ W) hyV _,
    hφ (U ⊓ W) inf_le_right _, tensorStalkIso_germ X y G M (U ⊓ W) hyV _ _, hgs]
  congr 1
  exact grpGerm_restrictₛₗ M (inf_le_right : U ⊓ W ≤ W) y hyV a

/-- **At a point where the fixed section is a basis of the stalk, the comparison is bijective on
that stalk.** -/
theorem bijective_stalkMapL_of_germ_basis (G M : SheafOfModules.{u} (structureSheafRing X))
    (φ : G ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj
      (G)).obj (M)))
    (W : Opens X.carrier) (a : M.val.obj (op W))
    (hφ : ∀ (V : Opens X.carrier) (h : V ≤ W) (s : G.val.obj (op V)),
      (φ.val.app (op V)).hom s = toTensorSheafSection X G M (op V)
        (s ⊗ₜ[X.presheaf.obj (op V)] ((M.val).restrictₛₗ ((homOfLE h).op)) a))
    (y : X.carrier) (hy : y ∈ W)
    (hbasis : Function.Bijective fun c : ringStalk X y => c • grpGerm X M.val y W hy a) :
    Function.Bijective (stalkMapL X G.val
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj
          (G)).obj (M))).val φ.val y) := by
  have hcomp : (tensorStalkIso X y G M) ∘
        (stalkMapL X G.val
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj
            (G)).obj (M))).val φ.val y)
      = fun g => g ⊗ₜ[ringStalk X y] grpGerm X M.val y W hy a :=
    funext fun g => tensorStalkIso_stalkMapL_eq G M φ W a hφ y hy g
  refine (Function.Bijective.of_comp_iff' (tensorStalkIso X y G M).bijective _).mp ?_
  rw [hcomp]
  exact TensorProduct.bijective_tmul_right _ hbasis

/-- A tensor product has no nonzero element in its stalk at a point where one factor has
none. -/
theorem subsingleton_grpStalk_tensorSheaf (G M : SheafOfModules.{u} (structureSheafRing X))
    (y : X.carrier) (h : Subsingleton (grpStalk X G.val y)) :
    Subsingleton (grpStalk X
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj
          (G)).obj (M))).val y) :=
  have : Subsingleton (TensorProduct (ringStalk X y) (grpStalk X G.val y)
      (grpStalk X M.val y)) := inferInstance
  ⟨fun _ _ => (tensorStalkIso X y G M).injective (Subsingleton.elim _ _)⟩

/-- **Where the stalk of the first factor vanishes, so does the stalk of the tensor product**,
and every morphism between them is bijective. -/
theorem bijective_stalkMapL_of_subsingleton (G M : SheafOfModules.{u} (structureSheafRing X))
    (φ : G ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj
      (G)).obj (M)))
    (y : X.carrier) (h : Subsingleton (grpStalk X G.val y)) :
    Function.Bijective (stalkMapL X G.val
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj
          (G)).obj (M))).val φ.val y) :=
  have := subsingleton_grpStalk_tensorSheaf G M y h
  ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

end Stacks.SheafOfModules.TensorStalkRingedSpace

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The sections of a sheaf of modules over an open set form a module over the sections of the
structure sheaf over that open set. -/
noncomputable local instance (moduleSheaf : X.Modules) (openSet : X.Opens) :
    Module (X.presheaf.obj (op openSet)) (moduleSheaf.val.obj (op openSet)) :=
  (moduleSheaf.val.obj (op openSet)).isModule

/-- The tensor product `G ⊗ M` of two sheaves of modules on a scheme `X`, as an object of
`X.Modules`. It is the same term as
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf`; the abbreviation exists so that its
declared type is `AlgebraicGeometry.Scheme.Modules`, which makes the section notation `Γ(-, U)`
and the module structure on sections available on it. A bare ascription
`(tensorSheaf X.toRingedSpace G M : X.Modules)` is forgotten before the `Γ` notation is
resolved. -/
noncomputable abbrev tensorModules (G M : X.Modules) : X.Modules :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor
    ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (G)).obj (M))

/-! ### The support of a tensor product -/

/-- Off the support of a sheaf of modules its stalk has no nonzero element. -/
theorem SheafOfModules.subsingleton_stalk_of_notMem_supp (G : X.Modules) {y : X}
    (hy : y ∉ SheafOfModules.supp G) : Subsingleton (grpStalk X.toRingedSpace G.val y) :=
  have h : ∀ z : grpStalk X.toRingedSpace G.val y, z = 0 := fun z => by
    by_contra hne
    exact hy ⟨z, hne⟩
  ⟨fun p q => (h p).trans (h q).symm⟩

/-- **The support of a tensor product is contained in the support of either factor.** The stalk
of the tensor product at `y` is the tensor product of the stalks (Tag 01CB), which has no
nonzero element once one factor has none. -/
theorem notMem_supp_tensorSheaf_of_notMem_supp (G M : X.Modules) {y : X}
    (hy : y ∉ SheafOfModules.supp G) :
    y ∉ SheafOfModules.supp (tensorModules G M) := by
  intro ⟨c, hc⟩
  exact hc ((subsingleton_grpStalk_tensorSheaf G M y
    (SheafOfModules.subsingleton_stalk_of_notMem_supp G hy)).elim _ _)

/-! ### Tensoring a section with a fixed section of the second factor -/

/-- **Tensoring with a fixed section of `M`.** For a section `a` of `M` over `W` and an open
`V ≤ W`, this is the map `s ↦ s ⊗ a|_V` on sections, landing in the sheafified tensor
product. -/
noncomputable def tmulSection (G M : X.Modules) (W : X.Opens) (a : Γ(M, W))
    (V : X.Opens) (hVW : V ≤ W) (s : Γ(G, V)) : Γ(tensorModules G M, V) :=
  toTensorSheafSection X.toRingedSpace G M (op V)
    (s ⊗ₜ[X.presheaf.obj (op V)] ((M.val).restrictₛₗ ((homOfLE hVW).op)) a)

/-- Tensoring with a fixed section `a` of `M` is additive in the section of `G`. -/
theorem tmulSection_add (G M : X.Modules) (W : X.Opens) (a : Γ(M, W))
    (V : X.Opens) (hVW : V ≤ W) (s s' : Γ(G, V)) :
    tmulSection G M W a V hVW (s + s')
      = tmulSection G M W a V hVW s + tmulSection G M W a V hVW s' :=
  (congrArg (toTensorSheafSection X.toRingedSpace G M (op V))
      (TensorProduct.add_tmul s s' (((M.val).restrictₛₗ ((homOfLE hVW).op)) a))).trans
    (toTensorSheafSection_add X.toRingedSpace G M (op V) _ _)

/-- Tensoring with a fixed section `a` of `M` is linear over the sections of the structure
sheaf. -/
theorem tmulSection_smul (G M : X.Modules) (W : X.Opens) (a : Γ(M, W))
    (V : X.Opens) (hVW : V ≤ W) (r : Γ(X, V)) (s : Γ(G, V)) :
    tmulSection G M W a V hVW (r • s) = r • tmulSection G M W a V hVW s :=
  (congrArg (toTensorSheafSection X.toRingedSpace G M (op V))
      (TensorProduct.smul_tmul' (R := X.presheaf.obj (op V)) r s
        (((M.val).restrictₛₗ ((homOfLE hVW).op)) a))).trans
    (toTensorSheafSection_smul X.toRingedSpace G M (op V) r
      (s ⊗ₜ[X.presheaf.obj (op V)] ((M.val).restrictₛₗ ((homOfLE hVW).op)) a))

/-- Tensoring with a fixed section `a` of `M` commutes with restriction along `V ≤ V'`. -/
theorem tmulSection_map (G M : X.Modules) (W : X.Opens) (a : Γ(M, W))
    (V V' : X.Opens) (hVV' : V ≤ V') (hV'W : V' ≤ W) (s : Γ(G, V')) :
    tmulSection G M W a V (hVV'.trans hV'W) (G.presheaf.map (homOfLE hVV').op s)
      = (tensorModules G M).presheaf.map (homOfLE hVV').op
          (tmulSection G M W a V' hV'W s) :=
  have hcomp := secRestr_secRestr (X := X.toRingedSpace) M.val hV'W hVV' a
  have key : (((G.val).restrictₛₗ ((homOfLE hVV').op)) s)
        ⊗ₜ[X.presheaf.obj (op V)]
        (((M.val).restrictₛₗ ((homOfLE (hVV'.trans hV'W)).op)) a)
      = ((PresheafOfModules.tensorObj (O := (X.toRingedSpace).presheaf) (G.val)
            (M.val)).restrictₛₗ ((homOfLE hVV').op)).toAddMonoidHom
          (s ⊗ₜ[X.presheaf.obj (op V')]
            ((M.val).restrictₛₗ ((homOfLE hV'W).op)) a) :=
    (congrArg (fun z => (((G.val).restrictₛₗ ((homOfLE hVV').op)) s)
        ⊗ₜ[X.presheaf.obj (op V)] z) hcomp).trans
      (PresheafOfModules.tensorObj_restrictₛₗ_tmul
        (O := X.toRingedSpace.presheaf) (F := G.val) (G := M.val) (homOfLE hVV').op s
        (((M.val).restrictₛₗ ((homOfLE hV'W).op)) a)).symm
  (congrArg (toTensorSheafSection X.toRingedSpace G M (op V)) key).trans
    (toTensorSheafSection_map (X := X.toRingedSpace) G M (homOfLE hVV').op _)

/-! ### Glueing the chartwise maps -/

/-- **The chartwise maps `s ↦ s ⊗ a_i|_V` glue.** Let `W` be a family of opens covering `X`, let
`a i` be a section of `M` over `W i`, and suppose that two *distinct* members of the family meet
only outside the support of `G`. Then there is a morphism `G ⟶ G ⊗ M` acting by `s ↦ s ⊗ a_i|_V`
on the sections over every open inside `W i`.

The agreement condition the glueing needs is free: over an open inside two distinct members the
sections of `G ⊗ M` form a subsingleton, the support of `G ⊗ M` being contained in that of
`G`. -/
theorem exists_hom_app_eq_tmulSection (G M : X.Modules) {ι : Type u} (W : ι → X.Opens)
    (hW : ∀ x : X, ∃ i, x ∈ W i) (a : ∀ i, Γ(M, W i))
    (hdisj : ∀ i j, i ≠ j → ∀ y : X, y ∈ W i → y ∈ W j → y ∉ SheafOfModules.supp G) :
    ∃ φ : G ⟶ tensorModules G M, ∀ (i : ι) (V : X.Opens) (h : V ≤ W i) (s : Γ(G, V)),
      φ.app V s = tmulSection G M (W i) (a i) V h s := by
  refine Stacks.AlgebraicGeometry.ModuleLimits.exists_hom_app_eq_of_cover W hW
    (fun i V h => tmulSection G M (W i) (a i) V h)
    (fun i V h => tmulSection_add G M (W i) (a i) V h)
    (fun i V h => tmulSection_smul G M (W i) (a i) V h)
    (fun i V V' h hV' => tmulSection_map G M (W i) (a i) V V' h hV') ?_
  intro i j V hi hj m
  by_cases hij : i = j
  · subst hij
    rfl
  · have : Subsingleton Γ(tensorModules G M, V) :=
      subsingleton_sections_of_avoiding_support (tensorModules G M) V fun y hy =>
        notMem_supp_tensorSheaf_of_notMem_supp G M (hdisj i j hij y (hi hy) (hj hy))
    exact Subsingleton.elim _ _

/-! ### An invertible sheaf has a local basis -/

/-- **An invertible sheaf of modules on a scheme has, around every point, a section whose germ
at that point is a basis of the stalk.** This is the converse half of Tag 0B8M read on one
stalk: `Stacks.SheafOfModules.exists_tensorPairing_eq_unitSection` produces the trivializing
pair of sections and
`Stacks.SheafOfModules.bijective_smul_germ_of_tensorPairing_eq_unitSection` reads off the
germ. -/
theorem exists_germ_basis_of_isInvertible
    (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] (x : X) :
    ∃ (W : X.Opens) (hx : x ∈ W) (a : M.val.obj (op W)),
      Function.Bijective fun c : ringStalk X.toRingedSpace x =>
        c • grpGerm X.toRingedSpace M.val x W hx a := by
  have hloc : ∀ z : X.toRingedSpace.carrier, IsLocalRing (ringStalk X.toRingedSpace z) :=
    fun z => X.isLocalRing z
  have hM : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property M :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property M).2 ‹_›
  obtain ⟨N, ⟨ψ⟩⟩ := (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit
    (O := X.toRingedSpace.presheaf)
    (hO := (structureSheafRing X.toRingedSpace).property) M).mp hM
  obtain ⟨W, hxW, a, b, hab⟩ := Stacks.SheafOfModules.exists_tensorPairing_eq_unitSection ψ x
  exact ⟨W, hxW, a, (Stacks.SheafOfModules.bijective_smul_germ_of_tensorPairing_eq_unitSection
    ψ a b hab x hxW).2⟩

/-! ### The isomorphism -/

/-- **An invertible sheaf does not move a coherent sheaf with zero-dimensional support**:
`ℱ ⊗_{𝒪_X} ℳ ≅ ℱ`. This is [Stacks, Tag 0AYT] at rank one, which is what the base case of Tag
0BEM's induction asks for; see the module docstring for the construction. -/
theorem nonempty_tensorModulesIso_of_topologicalKrullDim_supp_le_zero [IsLocallyNoetherian X]
    (G : X.Modules) [G.IsCoherent]
    (hG : topologicalKrullDim (SheafOfModules.supp G) ≤ 0) (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    Nonempty (tensorModules G M ≅ G) := by
  classical
  choose N hxN hN using fun x : ↥(SheafOfModules.supp G) =>
    exists_open_neighborhood_meets_support_singleton G hG x
  choose T hxT a hbasis using fun x : ↥(SheafOfModules.supp G) =>
    exists_germ_basis_of_isInvertible M (x : X)
  have : G.IsFiniteType := SheafOfModules.IsCoherent.isFiniteType
  let C : X.Opens := ⟨(SheafOfModules.supp G)ᶜ, (SheafOfModules.isClosed_supp G).isOpen_compl⟩
  let W : Option ↥(SheafOfModules.supp G) → X.Opens := fun i => i.elim C fun x => N x ⊓ T x
  have hW : ∀ y : X, ∃ i, y ∈ W i := fun y => by
    by_cases hy : y ∈ SheafOfModules.supp G
    · exact ⟨some ⟨y, hy⟩, hxN ⟨y, hy⟩, hxT ⟨y, hy⟩⟩
    · exact ⟨none, hy⟩
  have hdisj : ∀ i j, i ≠ j → ∀ y : X, y ∈ W i → y ∈ W j → y ∉ SheafOfModules.supp G := by
    intro i j hij y hi hj hys
    match i, j with
    | none, _ => exact hi hys
    | _, none => exact hj hys
    | some x, some x' =>
      exact hij (congrArg some (Subtype.ext
        ((hN x y hi.1 hys).symm.trans (hN x' y hj.1 hys))))
  obtain ⟨φ, hφ⟩ := exists_hom_app_eq_tmulSection G M W hW
    (fun i => match i with
      | none => 0
      | some x => M.presheaf.map (homOfLE (inf_le_right : N x ⊓ T x ≤ T x)).op (a x)) hdisj
  have hiso : IsIso φ := by
    refine Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_stalk φ fun y => ?_
    rw [ConcreteCategory.isIso_iff_bijective]
    by_cases hy : y ∈ SheafOfModules.supp G
    · refine bijective_stalkMapL_of_germ_basis G M φ (W (some ⟨y, hy⟩)) _
        (fun V h s => hφ (some ⟨y, hy⟩) V h s) y ⟨hxN ⟨y, hy⟩, hxT ⟨y, hy⟩⟩ ?_
      exact (grpGerm_restrictₛₗ M (inf_le_right : N ⟨y, hy⟩ ⊓ T ⟨y, hy⟩ ≤ T ⟨y, hy⟩) y
        ⟨hxN ⟨y, hy⟩, hxT ⟨y, hy⟩⟩ (a ⟨y, hy⟩)) ▸ hbasis ⟨y, hy⟩
    · exact bijective_stalkMapL_of_subsingleton G M φ y
        (SheafOfModules.subsingleton_stalk_of_notMem_supp G hy)
  exact ⟨(asIso φ).symm⟩

/-- **The base case of Tag 0BEM's induction, discharged.** This is
`AlgebraicGeometry.nonempty_tensorModulesIso_of_topologicalKrullDim_supp_le_zero` in the exact
shape the hypothesis `hbase` of
`AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_tensorInvertibleIso` is stated in: the
descent measure is `AlgebraicGeometry.natDimSupp`, and vanishing of it forces the dimension of
the support to be at most zero, because a scheme proper over a field has finite dimension
(`AlgebraicGeometry.coe_natDimSupp_eq`). -/
noncomputable def tensorInvertibleIso_of_natDimSupp (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (G : X.Modules)
    (hG : SheafOfModules.IsCoherent G) (hG0 : natDimSupp G = 0) (M : X.Modules)
    (hM : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
          (X.ringCatSheaf.2)⟩).obj (G)).obj (M)) :
      X.Modules) ≅ G := by
  have : G.IsCoherent := hG
  have : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M := hM
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hdim : topologicalKrullDim (SheafOfModules.supp G) ≤ 0 := by
    by_cases hsupp : SheafOfModules.supp G = ∅
    · rw [(topologicalKrullDim_supp_eq_bot_iff G).2 hsupp]
      exact bot_le
    · rw [← coe_natDimSupp_eq k f G hsupp, hG0]
      simp
  exact Classical.choice
    (nonempty_tensorModulesIso_of_topologicalKrullDim_supp_le_zero G hdim M)

/-- **[Stacks, Tag 0BEM] from `hstep` alone.** The Euler characteristics of the twists
`ℱ ⊗ 𝓛_1^{⊗ n_1} ⊗ ⋯ ⊗ 𝓛_r^{⊗ n_r}` of a coherent sheaf on a proper scheme over a field are the
values of a rational polynomial which is zero or of total degree at most `dim Supp ℱ`, provided
the first-difference identity of the source's second paragraph.

This is `AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_natDimSupp` with its
hypothesis `hbase` discharged by `AlgebraicGeometry.tensorInvertibleIso_of_natDimSupp`. The
remaining hypothesis `hstep` is the source's own first-difference identity, which it obtains
from a regular meromorphic section of `𝓛_i` and its ideal of denominators. -/
theorem exists_eulerPolynomial_twistedSheaf_of_hstep (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] {r : ℕ} (L : Fin r → X.Modules)
    [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L i)]
    (hstep : ∀ (G : X.Modules) (hG : SheafOfModules.IsCoherent G), natDimSupp G ≠ 0 →
      ∀ i : Fin r,
      ∃ (G₁ G₂ : X.Modules) (hG₁ : SheafOfModules.IsCoherent G₁)
        (hG₂ : SheafOfModules.IsCoherent G₂),
        natDimSupp G₁ < natDimSupp G ∧ natDimSupp G₂ < natDimSupp G ∧
        ∀ n : Fin r → ℤ,
          (@eulerCharacteristic k _ X f _ (twistedSheaf G L (Function.update n i (n i + 1)))
              (@twistedSheaf_isCoherent X r G L _ hG _) : ℚ)
            - (@eulerCharacteristic k _ X f _ (twistedSheaf G L n)
                (@twistedSheaf_isCoherent X r G L _ hG n) : ℚ)
            = (@eulerCharacteristic k _ X f _ (twistedSheaf G₁ L n)
                (@twistedSheaf_isCoherent X r G₁ L _ hG₁ n) : ℚ)
              - (@eulerCharacteristic k _ X f _ (twistedSheaf G₂ L n)
                  (@twistedSheaf_isCoherent X r G₂ L _ hG₂ n) : ℚ))
    (F : X.Modules) (hF : SheafOfModules.IsCoherent F) :
    ∃ P : MvPolynomial (Fin r) ℚ,
      (P = 0 ∨ (P.totalDegree : WithBot ℕ∞) ≤
        topologicalKrullDim (SheafOfModules.supp F)) ∧
      ∀ n : Fin r → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P
        = (@eulerCharacteristic k _ X f _ (twistedSheaf F L n)
            (@twistedSheaf_isCoherent X r F L _ hF n) : ℚ) :=
  exists_eulerPolynomial_twistedSheaf_of_tensorInvertibleIso L k f natDimSupp
    (fun G hG hG0 M hM => tensorInvertibleIso_of_natDimSupp k f G hG hG0 M hM)
    hstep F hF fun hsupp => le_of_eq (coe_natDimSupp_eq k f F hsupp)

end AlgebraicGeometry

end
