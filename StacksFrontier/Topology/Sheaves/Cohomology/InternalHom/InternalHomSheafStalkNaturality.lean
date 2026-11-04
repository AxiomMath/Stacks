module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkColimit
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.InternalHomSheafAsSheafHom
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.InternalHomSheafUnitEvaluation
import StacksCore.Tactic.StacksAttribute

/-!
# Naturality of the stalk of an internal Hom sheaf in its source

Let `Rc` be a sheaf of commutative rings on a topological space `X`, write `O_X` for the
underlying sheaf of rings, and let `F`, `G` be `O_X`-modules. Stacks 01CP provides the canonical
`O_{X,x}`-linear map

`SheafHom_{O_X}(F, G)_x ⟶ (F_x →ₗ[O_{X,x}] G_x)`,

available as `Stacks.SheafOfModules.SheafHomStalk.sheafHomStalkLinearMap`, and says it is an
isomorphism when `F` is of finite presentation. What 01CP does not record is that the canonical
map is *natural in the source*: a morphism `β : F₁ ⟶ F` induces a precomposition map of internal
Hom sheaves, and the square relating the two canonical maps commutes.

This file proves that naturality. It is needed to apply 01CP degreewise to a complex: the
differential of `SheafHom(K, G)` is built from the precomposition maps along the differentials of
`K`, so without the commuting square the degreewise stalk identifications do not assemble into
an identification of complexes.

Nothing here assumes anything about `F₁`, `F` or `G`: naturality is a property of the canonical
map, not of the isomorphism, so it holds with no finiteness hypothesis. Finite presentation
enters only in the final corollary, which upgrades the naturality square to a square of linear
equivalences.

## Main definitions

* `Stacks.SheafOfModules.SheafHomStalk.modStalkMap`: the stalk at `x` of a morphism of
  `O_X`-modules, as an `O_{X,x}`-linear map of stalks.
* `Stacks.SheafOfModules.SheafHomStalk.modStalkMapAddHom`: the same, as an additive map on
  morphisms.

## Main statements

* `Stacks.SheafOfModules.SheafHomStalk.modStalkMap_id`,
  `Stacks.SheafOfModules.SheafHomStalk.modStalkMap_comp`,
  `Stacks.SheafOfModules.SheafHomStalk.modStalkMap_add`,
  `Stacks.SheafOfModules.SheafHomStalk.modStalkMap_zero`,
  `Stacks.SheafOfModules.SheafHomStalk.modStalkMap_neg`,
  `Stacks.SheafOfModules.SheafHomStalk.modStalkMap_zsmul`: taking stalks is functorial and
  additive in the morphism. The differential of an internal Hom complex is a signed sum of pre-
  and post-composition maps, so these are what let the naturality squares below be applied to a
  differential rather than to a single morphism.

* `Stacks.SheafOfModules.SheafHomStalk.sheafHomStalkLinearMap_naturality_isPrecomp`: for a
  precomposition map `m` along `β : F₁ ⟶ F`, the canonical map of 01CP for `F₁` applied to the
  stalk of `m` is the canonical map for `F` followed by precomposition with the stalk of `β`.
* `Stacks.SheafOfModules.SheafHomStalk.sheafHomStalkLinearMap_naturality_isPostcomp`: the
  companion statement in the target variable, for a postcomposition map along `u : G ⟶ G₁`.
* `Stacks.SheafOfModules.internalHomSheafStalkEquiv_naturality`: the 01CP identification
  `Hom_{O_X}(F, G)_x ≃ (F_x →ₗ G_x)` is natural in `F`, for `F` and `F₁` of finite presentation.

## Implementation notes

The stalk of a morphism is taken in the spelling `Stacks.ModuleSkyscraper.stalkMapLinear`, whose
germ formula `stalkMapLinear_germ` is stated at `TopCat.Presheaf.germ` of the underlying presheaf
— which is what `Stacks.SheafOfModules.SheafHomStalk.germAt` unfolds to. So the two germ formulas
compose with no transport.

Both naturality squares are proved by evaluating on a germ. Since a germ of the internal Hom and
a germ of the source are a priori taken over different opens, each proof first shrinks the two
opens to their intersection, exactly as `sheafHomStalkLinearMap_unique` does; after that the
section-level identity is the associativity of composition, which holds by `rfl` because the
component of a restricted morphism at the identity object of the slice site is the component of
the morphism itself.

## References

* [Stacks Project, Tag 01CP](https://stacks.math.columbia.edu/tag/01CP)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules.SheafHomStalk

variable {X : TopCat.{u}} {Rc : TopCat.Sheaf CommRingCat.{u} X}

section StalkMapOfMorphism

/-- The stalk at `x` of a morphism of `O_X`-modules, as an `O_{X,x}`-linear map of stalks. -/
abbrev modStalkMap {M N : SheafOfModules.{u} (structureSheaf Rc)} (f : M ⟶ N) (x : X) :
    modStalk M x →ₗ[ringStalk Rc x] modStalk N x :=
  Stacks.ModuleSkyscraper.stalkMapLinear (R := Rc.obj)
    (M := commVal (Rc := Rc) M) (N := commVal (Rc := Rc) N) f.val x

/-- The stalk of a morphism sends the germ of a section to the germ of its image. -/
lemma modStalkMap_germ {M N : SheafOfModules.{u} (structureSheaf Rc)} (f : M ⟶ N) (x : X)
    (U : Opens X) (hxU : x ∈ U) (t : (commVal (Rc := Rc) M).obj (op U)) :
    modStalkMap f x (germAt M U x hxU t) = germAt N U x hxU (f.val.app (op U) t) :=
  Stacks.ModuleSkyscraper.stalkMapLinear_germ (R := Rc.obj) f.val x U hxU t

/-- Two `O_{X,x}`-linear maps out of a stalk agree as soon as they agree on germs. -/
lemma modStalk_linearMap_ext {M : SheafOfModules.{u} (structureSheaf Rc)} {x : X}
    {P : Type u} [AddCommGroup P] [Module (ringStalk Rc x) P]
    {ψ₁ ψ₂ : modStalk M x →ₗ[ringStalk Rc x] P}
    (h : ∀ (U : Opens X) (hxU : x ∈ U) (t : (commVal (Rc := Rc) M).obj (op U)),
      ψ₁ (germAt M U x hxU t) = ψ₂ (germAt M U x hxU t)) :
    ψ₁ = ψ₂ := by
  refine LinearMap.ext fun σ ↦ ?_
  obtain ⟨U, hxU, t, rfl⟩ := exists_germ_eq M σ
  exact h U hxU t

variable {M N P : SheafOfModules.{u} (structureSheaf Rc)}

/-- The stalk of the identity is the identity. -/
@[simp]
lemma modStalkMap_id (x : X) : modStalkMap (𝟙 M) x = LinearMap.id :=
  modStalk_linearMap_ext fun U hxU t ↦ modStalkMap_germ (𝟙 M) x U hxU t

/-- Taking stalks is functorial. -/
lemma modStalkMap_comp (f : M ⟶ N) (g : N ⟶ P) (x : X) :
    modStalkMap (f ≫ g) x = (modStalkMap g x).comp (modStalkMap f x) :=
  modStalk_linearMap_ext fun U hxU t ↦ by
    rw [modStalkMap_germ, LinearMap.comp_apply, modStalkMap_germ, modStalkMap_germ]
    rfl

/-- Taking stalks is additive in the morphism. This is what lets the naturality square be
applied to a differential of an internal Hom complex, whose components are signed sums of pre-
and post-composition maps. -/
lemma modStalkMap_add (f g : M ⟶ N) (x : X) :
    modStalkMap (f + g) x = modStalkMap f x + modStalkMap g x :=
  modStalk_linearMap_ext fun U hxU t ↦ by
    rw [modStalkMap_germ, LinearMap.add_apply, modStalkMap_germ, modStalkMap_germ,
      ← germAt_add]
    rfl

/-- The stalk of the zero morphism is zero. -/
@[simp]
lemma modStalkMap_zero (x : X) : modStalkMap (0 : M ⟶ N) x = 0 :=
  modStalk_linearMap_ext fun U hxU t ↦ by
    rw [modStalkMap_germ, LinearMap.zero_apply,
      show ((0 : M ⟶ N).val.app (op U)) t = 0 from rfl, germAt_zero]

/-- Taking the stalk at `x`, packaged as an additive map on morphisms. -/
def modStalkMapAddHom (M N : SheafOfModules.{u} (structureSheaf Rc)) (x : X) :
    (M ⟶ N) →+ (modStalk M x →ₗ[ringStalk Rc x] modStalk N x) where
  toFun f := modStalkMap f x
  map_zero' := modStalkMap_zero x
  map_add' f g := modStalkMap_add f g x

/-- The stalk of a negated morphism is the negation of the stalk. -/
lemma modStalkMap_neg (f : M ⟶ N) (x : X) : modStalkMap (-f) x = -modStalkMap f x :=
  map_neg (modStalkMapAddHom M N x) f

/-- The stalk of an integer multiple of a morphism is that multiple of the stalk. The signs in
the differential of an internal Hom complex make this the form in which additivity is used. -/
lemma modStalkMap_zsmul (n : ℤ) (f : M ⟶ N) (x : X) :
    modStalkMap (n • f) x = n • modStalkMap f x :=
  map_zsmul (modStalkMapAddHom M N x) n f

end StalkMapOfMorphism

section Naturality

variable {F₁ F G G₁ : SheafOfModules.{u} (structureSheaf Rc)}

/-- Evaluating a morphism restricted to the slice over `U` at the identity object of that slice
is evaluating the morphism itself at `U`; so precomposing a homomorphism `F|_U ⟶ G|_U` with the
restriction of `β : F₁ ⟶ F` acts on sections over `U` as the component of `β` at `U` followed by
the component of the homomorphism. -/
lemma appAt_over_comp (β : F₁ ⟶ F) {U : Opens X} (φ : F.over U ⟶ G.over U)
    (t : (commVal (Rc := Rc) F₁).obj (op U)) :
    appAt le_rfl (β.over U ≫ φ) t = appAt le_rfl φ (β.val.app (op U) t) :=
  rfl

/-- Postcomposing a homomorphism `F|_U ⟶ G|_U` with the restriction of `u : G ⟶ G₁` acts on
sections over `U` as the component of the homomorphism followed by the component of `u` at `U`. -/
lemma appAt_comp_over (u : G ⟶ G₁) {U : Opens X} (φ : F.over U ⟶ G.over U)
    (t : (commVal (Rc := Rc) F).obj (op U)) :
    appAt le_rfl (φ ≫ u.over U) t = u.val.app (op U) (appAt le_rfl φ t) :=
  rfl

/-- Two stalk elements at `x` are germs of sections over one common open neighbourhood of `x`. -/
private lemma exists_germ_eq_common {M N : SheafOfModules.{u} (structureSheaf Rc)} {x : X}
    (σ : modStalk M x) (τ : modStalk N x) :
    ∃ (U : Opens X) (hxU : x ∈ U) (s : (commVal (Rc := Rc) M).obj (op U))
      (t : (commVal (Rc := Rc) N).obj (op U)),
      σ = germAt M U x hxU s ∧ τ = germAt N U x hxU t := by
  obtain ⟨U, hxU, s, rfl⟩ := exists_germ_eq M σ
  obtain ⟨W, hxW, t, rfl⟩ := exists_germ_eq N τ
  have hxZ : x ∈ W ⊓ U := mem_inf hxW hxU
  exact ⟨W ⊓ U, hxZ, resLE M inf_le_right s, resLE N inf_le_left t,
    (germAt_resLE M inf_le_right hxZ s).symm, (germAt_resLE N inf_le_left hxZ t).symm⟩

/-- **Naturality of the canonical map of Stacks 01CP in the source.** Let `β : F₁ ⟶ F` be a
morphism of `O_X`-modules and let `m : H.obj ⟶ H'.obj` be the precomposition map along `β`
between realizations `H` of `SheafHom(F, G)` and `H'` of `SheafHom(F₁, G)`. Then the canonical
map of 01CP for `F₁`, applied to the stalk of `m`, is the canonical map for `F` followed by
precomposition with the stalk of `β`. There is no hypothesis on `F₁`, `F` or `G`. -/
theorem sheafHomStalkLinearMap_naturality_isPrecomp (β : F₁ ⟶ F)
    (H : SheafHom Rc F G) (H' : SheafHom Rc F₁ G) {m : H.obj ⟶ H'.obj}
    (hm : SheafHom.IsPrecomp Rc β H H' m) (x : X) (σ : modStalk H.obj x) :
    sheafHomStalkLinearMap H' x (modStalkMap m x σ)
      = (sheafHomStalkLinearMap H x σ).comp (modStalkMap β x) := by
  refine LinearMap.ext fun n ↦ ?_
  obtain ⟨U, hxU, s, t, rfl, rfl⟩ := exists_germ_eq_common σ n
  rw [modStalkMap_germ m x U hxU, sheafHomStalkLinearMap_germ H' U hxU, hm U s,
    LinearMap.comp_apply, modStalkMap_germ β x U hxU, sheafHomStalkLinearMap_germ H U hxU,
    appAt_over_comp]

/-- **Naturality of the canonical map of Stacks 01CP in the target.** Let `u : G ⟶ G₁` be a
morphism of `O_X`-modules and let `m : H.obj ⟶ H'.obj` be the postcomposition map along `u`
between realizations `H` of `SheafHom(F, G)` and `H'` of `SheafHom(F, G₁)`. Then the canonical
map of 01CP for `G₁`, applied to the stalk of `m`, is the canonical map for `G` followed by
postcomposition with the stalk of `u`. There is no hypothesis on `F`, `G` or `G₁`. -/
theorem sheafHomStalkLinearMap_naturality_isPostcomp (u : G ⟶ G₁)
    (H : SheafHom Rc F G) (H' : SheafHom Rc F G₁) {m : H.obj ⟶ H'.obj}
    (hm : SheafHom.IsPostcomp Rc u H H' m) (x : X) (σ : modStalk H.obj x) :
    sheafHomStalkLinearMap H' x (modStalkMap m x σ)
      = (modStalkMap u x).comp (sheafHomStalkLinearMap H x σ) := by
  refine LinearMap.ext fun n ↦ ?_
  obtain ⟨U, hxU, s, t, rfl, rfl⟩ := exists_germ_eq_common σ n
  rw [modStalkMap_germ m x U hxU, sheafHomStalkLinearMap_germ H' U hxU, hm U s,
    LinearMap.comp_apply, sheafHomStalkLinearMap_germ H U hxU, appAt_comp_over,
    modStalkMap_germ u x U hxU]

end Naturality

end Stacks.SheafOfModules.SheafHomStalk

namespace Stacks.SheafOfModules

open Stacks.SheafOfModules.SheafHomStalk

variable {X : TopCat.{u}} {Rc : TopCat.Sheaf CommRingCat.{u} X}
  {F₁ F G : SheafOfModules.{u} (structureSheaf Rc)}

variable [F.IsFinitePresentation] [F₁.IsFinitePresentation]

/-- **The 01CP stalk identification is natural in the source.** For `F` and `F₁` of finite
presentation and `β : F₁ ⟶ F`, the identification
`Hom_{O_X}(F, G)_x ≃ (F_x →ₗ[O_{X,x}] G_x)` of `internalHomSheafStalkEquiv` carries the stalk of
the precomposition map along `β` to precomposition with the stalk of `β`. -/
theorem internalHomSheafStalkEquiv_naturality (β : F₁ ⟶ F) (x : X)
    (σ : modStalk (RingedSite.internalHomSheaf (ringedSite Rc) F G) x) :
    internalHomSheafStalkEquiv Rc F₁ G x
        (modStalkMap (RingedSite.internalHomPre (ringedSite Rc) β) x σ)
      = (internalHomSheafStalkEquiv Rc F G x σ).comp (modStalkMap β x) := by
  have h := sheafHomStalkLinearMap_naturality_isPrecomp β (internalHomSheafHom Rc F G)
    (internalHomSheafHom Rc F₁ G) (isPrecomp_internalHomPre Rc β G) x σ
  rw [← (sheafHomStalkLinearEquivOfFinitePresentation
      (internalHomSheafHom Rc F₁ G) x).toLinearMap_eq] at h
  rw [← (sheafHomStalkLinearEquivOfFinitePresentation
      (internalHomSheafHom Rc F G) x).toLinearMap_eq] at h
  exact h

end Stacks.SheafOfModules

end
