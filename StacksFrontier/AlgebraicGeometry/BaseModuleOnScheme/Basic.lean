module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme

/-!
# `V ⊗ 𝒪_X` for a module over the base ring of a scheme

Let `X` be a scheme over the spectrum of a commutative ring `k`, by way of a structure morphism
`π : X ⟶ Spec k`, and let `V` be a `k`-module. The **constant module `V ⊗ 𝒪_X`** is the inverse
image along `π` of the quasi-coherent module `Ṽ` on `Spec k`:

`V ⊗ 𝒪_X = π^* Ṽ`.

It is quasi-coherent, functorial in `V`, functorial in `X` over `Spec k`, and its morphisms out
of it are exactly the `k`-linear maps out of `V`:

`Hom_{𝒪_X}(V ⊗ 𝒪_X, M) ≃ Hom_k(V, Γ(X, M))`.

The last is the only handle on the object that is ever needed to *write down* a morphism out of
it, and it is the reason the construction is set up as a composite of two adjoints rather than as
a sheafification of `U ↦ V ⊗_k Γ(X, U)`.

## Main definitions

* `Stacks.AlgebraicGeometry.BaseModuleOnScheme.tensorFunctor`: the functor
  `V ↦ V ⊗ 𝒪_X`, `ModuleCat k ⥤ X.Modules`.
* `Stacks.AlgebraicGeometry.BaseModuleOnScheme.tensorStructureSheaf`: the module `V ⊗ 𝒪_X`.
* `Stacks.AlgebraicGeometry.BaseModuleOnScheme.globalSectionsFunctor`: the global sections of a
  module on `X`, read as a `k`-module through `π`.
* `Stacks.AlgebraicGeometry.BaseModuleOnScheme.adjunction`: the adjunction
  `(- ⊗ 𝒪_X) ⊣ Γ(X, -)`, as a composite of the tilde–global-sections adjunction on `Spec k` with
  the inverse-image–direct-image adjunction of `π`.
* `Stacks.AlgebraicGeometry.BaseModuleOnScheme.toSections`: the canonical `k`-linear map
  `V → Γ(X, V ⊗ 𝒪_X)`, the unit of that adjunction.
* `Stacks.AlgebraicGeometry.BaseModuleOnScheme.ofSections`: the morphism `V ⊗ 𝒪_X ⟶ M` attached
  to a `k`-linear map `V → Γ(X, M)`.

## Main results

* `Stacks.AlgebraicGeometry.BaseModuleOnScheme.isQuasicoherent_tensorStructureSheaf`:
  **`V ⊗ 𝒪_X` is quasi-coherent**, for every `k`-module `V` and every scheme over `Spec k`.
* `Stacks.AlgebraicGeometry.BaseModuleOnScheme.homEquiv`: **the universal property**, a morphism
  `V ⊗ 𝒪_X ⟶ M` is a `k`-linear map `V → Γ(X, M)`.
* `Stacks.AlgebraicGeometry.BaseModuleOnScheme.hom_ext`: two morphisms out of `V ⊗ 𝒪_X` agreeing
  on the image of `V` in global sections are equal.
* `Stacks.AlgebraicGeometry.BaseModuleOnScheme.unitIso`: **`k ⊗ 𝒪_X ≅ 𝒪_X`.**
* `Stacks.AlgebraicGeometry.BaseModuleOnScheme.freeIso`: **`(ι →₀ k) ⊗ 𝒪_X ≅ 𝒪_X^{(ι)}`**, so a
  free `k`-module gives a free module on `X`.
* `Stacks.AlgebraicGeometry.BaseModuleOnScheme.pullbackIso`: **functoriality in `X`**, the
  inverse image of `V ⊗ 𝒪_X` along a morphism of schemes over `Spec k` is `V ⊗ 𝒪_{X'}`.

## Implementation notes

Quasi-coherence is not proved here: `Ṽ` is quasi-coherent in Mathlib and the inverse image of a
quasi-coherent module along an arbitrary morphism of schemes is quasi-coherent by Tag 01BG,
available in instance form as `Stacks.Modules.instIsQuasicoherentPullbackObj`. In particular no
finiteness or freeness of `V` is needed anywhere in this file.

The global sections are read through `AlgebraicGeometry.moduleSpecΓFunctor`, whose value is an
honest object of `ModuleCat k`; composing with the direct image along `π` is what makes the
universal property a statement about `k`-linear maps. The underlying type of
`(globalSectionsFunctor π).obj M` is `Γ(M, π ⁻¹ᵁ ⊤)`, which is `Γ(M, ⊤)` up to the equality
`π ⁻¹ᵁ ⊤ = ⊤`; it is left in the pullback form, because that is the form in which
`AlgebraicGeometry.Scheme.Modules.pushforward_obj_obj` holds by `rfl` and the form the
adjunction's unit and counit are stated at.

`Stacks.AlgebraicGeometry.BaseModuleOnScheme.unitIso` and `...freeIso` are the two places where
the construction is computed rather than used abstractly, and both come from Mathlib:
`AlgebraicGeometry.tildeSelf` and `AlgebraicGeometry.tildeFinsupp` identify `Ṽ` for `V = k` and
`V = (ι →₀ k)`, and `SheafOfModules.pullbackObjUnitToUnit` and
`SheafOfModules.pullbackObjFreeIso` carry those identifications through the inverse image.

## References

* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 01AI](https://stacks.math.columbia.edu/tag/01AI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.BaseModuleOnScheme

variable {k : CommRingCat.{u}} {X X' : Scheme.{u}}

/-! ### The construction and its universal property -/

/-- **`V ↦ V ⊗ 𝒪_X`**, the constant-module functor of a scheme over `Spec k`: the inverse image
along the structure morphism of the quasi-coherent module attached to a `k`-module. -/
def tensorFunctor (π : X ⟶ Spec k) : ModuleCat.{u} k ⥤ X.Modules :=
  AlgebraicGeometry.tilde.functor k ⋙ Scheme.Modules.pullback π

/-- **`V ⊗ 𝒪_X`**, the module on a scheme over `Spec k` attached to a module over the base
ring. -/
abbrev tensorStructureSheaf (π : X ⟶ Spec k) (V : ModuleCat.{u} k) : X.Modules :=
  (tensorFunctor π).obj V

/-- The global sections of a module on a scheme over `Spec k`, read as a module over `k`. -/
abbrev globalSectionsFunctor (π : X ⟶ Spec k) : X.Modules ⥤ ModuleCat.{u} k :=
  Scheme.Modules.pushforward π ⋙ AlgebraicGeometry.moduleSpecΓFunctor

/-- **The adjunction `(- ⊗ 𝒪_X) ⊣ Γ(X, -)`.** -/
def adjunction (π : X ⟶ Spec k) : tensorFunctor π ⊣ globalSectionsFunctor π :=
  AlgebraicGeometry.tilde.adjunction.comp (Scheme.Modules.pullbackPushforwardAdjunction π)

/-- **`V ⊗ 𝒪_X` is quasi-coherent**, by Tag 01BG: `Ṽ` is quasi-coherent on `Spec k` and the
inverse image of a quasi-coherent module along an arbitrary morphism of schemes is
quasi-coherent. -/
instance isQuasicoherent_tensorStructureSheaf (π : X ⟶ Spec k) (V : ModuleCat.{u} k) :
    (tensorStructureSheaf π V).IsQuasicoherent :=
  inferInstanceAs ((Scheme.Modules.pullback π).obj (AlgebraicGeometry.tilde V)).IsQuasicoherent

/-- **The universal property of `V ⊗ 𝒪_X`**: a morphism of `𝒪_X`-modules out of it is exactly a
`k`-linear map out of `V` into the global sections of the target. -/
def homEquiv (π : X ⟶ Spec k) (V : ModuleCat.{u} k) (M : X.Modules) :
    (tensorStructureSheaf π V ⟶ M) ≃ (V ⟶ (globalSectionsFunctor π).obj M) :=
  (adjunction π).homEquiv V M

/-- **The canonical `k`-linear map `V → Γ(X, V ⊗ 𝒪_X)`**, the unit of the adjunction. -/
def toSections (π : X ⟶ Spec k) (V : ModuleCat.{u} k) :
    V ⟶ (globalSectionsFunctor π).obj (tensorStructureSheaf π V) :=
  (adjunction π).unit.app V

/-- **The morphism `V ⊗ 𝒪_X ⟶ M` attached to a `k`-linear map `V → Γ(X, M)`.** -/
def ofSections (π : X ⟶ Spec k) {V : ModuleCat.{u} k} {M : X.Modules}
    (f : V ⟶ (globalSectionsFunctor π).obj M) : tensorStructureSheaf π V ⟶ M :=
  (homEquiv π V M).symm f

/-- The `k`-linear map attached to `ofSections π f` is `f`. -/
@[simp]
theorem homEquiv_ofSections (π : X ⟶ Spec k) {V : ModuleCat.{u} k} {M : X.Modules}
    (f : V ⟶ (globalSectionsFunctor π).obj M) : homEquiv π V M (ofSections π f) = f :=
  (homEquiv π V M).apply_symm_apply f

/-- The morphism attached to the `k`-linear map `homEquiv π V M g` is `g`. -/
@[simp]
theorem ofSections_homEquiv (π : X ⟶ Spec k) {V : ModuleCat.{u} k} {M : X.Modules}
    (g : tensorStructureSheaf π V ⟶ M) : ofSections π (homEquiv π V M g) = g :=
  (homEquiv π V M).symm_apply_apply g

/-- The `k`-linear map attached to a morphism `g` out of `V ⊗ 𝒪_X` is the composite of
`toSections π V` with the image of `g` on global sections. -/
theorem homEquiv_apply (π : X ⟶ Spec k) {V : ModuleCat.{u} k} {M : X.Modules}
    (g : tensorStructureSheaf π V ⟶ M) :
    homEquiv π V M g = toSections π V ≫ (globalSectionsFunctor π).map g := by
  rw [homEquiv, toSections, Adjunction.homEquiv_unit]

/-- **Two morphisms out of `V ⊗ 𝒪_X` with the same restriction to `V` are equal.** -/
theorem hom_ext (π : X ⟶ Spec k) {V : ModuleCat.{u} k} {M : X.Modules}
    {g h : tensorStructureSheaf π V ⟶ M}
    (H : toSections π V ≫ (globalSectionsFunctor π).map g =
      toSections π V ≫ (globalSectionsFunctor π).map h) : g = h :=
  (homEquiv π V M).injective (by rw [homEquiv_apply, homEquiv_apply, H])

/-- The functorial image of `f : V ⟶ W` followed by the morphism attached to a `k`-linear map out
of `W` is the morphism attached to the composite `k`-linear map. -/
@[reassoc]
theorem map_comp_ofSections (π : X ⟶ Spec k) {V W : ModuleCat.{u} k} (f : V ⟶ W)
    {M : X.Modules} (g : W ⟶ (globalSectionsFunctor π).obj M) :
    (tensorFunctor π).map f ≫ ofSections π g = ofSections π (f ≫ g) :=
  ((adjunction π).homEquiv_naturality_left_symm f g).symm

/-! ### The computed cases -/

/-- **`k ⊗ 𝒪_X ≅ 𝒪_X`.** -/
def unitIso (π : X ⟶ Spec k) :
    tensorStructureSheaf π (ModuleCat.of k k) ≅ AlgebraicGeometry.Scheme.unitModule X :=
  (Scheme.Modules.pullback π).mapIso AlgebraicGeometry.tildeSelf ≪≫
    Scheme.Modules.pullbackUnitIso π

/-- **`(ι →₀ k) ⊗ 𝒪_X ≅ 𝒪_X^{(ι)}`**: a free module over the base ring gives a free module on the
scheme, on the same index type. -/
def freeIso (π : X ⟶ Spec k) (ι : Type u) :
    tensorStructureSheaf π (ModuleCat.of k (ι →₀ k)) ≅ SheafOfModules.free.{u} ι :=
  have : (TopologicalSpace.Opens.map π.base).Final :=
    CategoryTheory.final_of_representablyFlat _
  have : (SheafOfModules.pushforward π.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction π).isRightAdjoint
  (Scheme.Modules.pullback π).mapIso (AlgebraicGeometry.tildeFinsupp ι) ≪≫
    SheafOfModules.pullbackObjFreeIso π.toRingCatSheafHom ι

/-! ### Functoriality in the scheme -/

/-- **Functoriality in the scheme**: the inverse image of `V ⊗ 𝒪_X` along a morphism of schemes
over `Spec k` is `V ⊗ 𝒪_{X'}`. -/
def pullbackIso {π : X ⟶ Spec k} {π' : X' ⟶ Spec k} (f : X' ⟶ X) (hf : f ≫ π = π')
    (V : ModuleCat.{u} k) :
    (Scheme.Modules.pullback f).obj (tensorStructureSheaf π V) ≅ tensorStructureSheaf π' V :=
  (Scheme.Modules.pullbackComp f π).app (AlgebraicGeometry.tilde V) ≪≫
    (Scheme.Modules.pullbackCongr hf).app (AlgebraicGeometry.tilde V)

end Stacks.AlgebraicGeometry.BaseModuleOnScheme

end
