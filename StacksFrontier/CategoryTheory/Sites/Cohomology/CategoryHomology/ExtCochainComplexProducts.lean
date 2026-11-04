module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.ExtCochainComplex
import StacksCore.Tactic.StacksAttribute

/-!
# Direct sums and products in the cochain complex computing homomorphisms

Let `C` be a small category carrying the chaotic topology, let `O : Cᵒᵖ ⥤ RingCat` be a sheaf of
rings on it, and let `K^•(G, F)` be the cochain complex of `Stacks.CategoryExt.extCochainComplex`.
Stacks 08S0 asserts that the bifunctor `(G, F) ↦ K^•(G, F)` transforms direct sums in the first
variable into products and commutes with products in the second variable. This file proves both
halves, for direct sums and for products indexed by an arbitrary type.

## Main results

* `Stacks.CategoryExt.isLimitExtCochainComplexFanOfDirectSum`: if an `O`-module is the direct sum
  of a family `Gᵢ` of `O`-modules, then the complexes `K^•(Gᵢ, F)`, together with the maps the
  bifunctor induces from the inclusions of the summands, exhibit the complex of the direct sum as
  their product.
* `Stacks.CategoryExt.isLimitExtCochainComplexFanOfProduct`: if an `O`-module is the product of a
  family `Fᵢ` of `O`-modules, then the complexes `K^•(G, Fᵢ)`, together with the maps the
  bifunctor induces from the projections, exhibit the complex of the product as their product.

## Implementation notes

The degree-`n` cochains take `Hom` over the ring `O(Uₙ)` at the far end of the string of arrows,
so a cochain is semilinear along the restriction map `O(Uₙ) ⟶ O(U₀)`, and the universal property
of a direct sum for linear maps, `DirectSum.toModule`, does not reach the first variable. No
semilinear universal property of a direct sum is built here. Instead
`Stacks.CategoryExt.toRestrictScalars` reads a semilinear map as a morphism of `O(Uₙ)`-modules
into a restriction of scalars, with the same underlying function; the universal property then
needed is that of the coproduct in `ModuleCat (O(Uₙ))`, and `PresheafOfModules.evaluation` already
carries a direct sum of `O`-modules to one. The second variable is dual, and uses in addition that
restriction of scalars preserves limits.

Both halves are reduced to the cochains of a single degree by `HomologicalComplex.isLimitOfEval`.
In each degree the comparison is an additive equivalence onto the product type, which
`Stacks.CategoryExt.isLimitFanOfAddEquiv` turns into a limit fan.

## References

* [Stacks Project, Tag 08S0](https://stacks.math.columbia.edu/tag/08S0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v m t

namespace Stacks.CategoryExt

section RestrictScalars

variable {R S : Type*} [Ring R] [Ring S] {σ : R →+* S}
  {M : ModuleCat.{m} R} {N : ModuleCat.{m} S}

/-- A `σ`-semilinear map `M ⟶ N` read as a morphism of `R`-modules into the restriction of
scalars of `N` along `σ`, which has the same underlying function. -/
def toRestrictScalars (φ : M →ₛₗ[σ] N) : M ⟶ (ModuleCat.restrictScalars σ).obj N :=
  ModuleCat.ofHom (X := M) (Y := (ModuleCat.restrictScalars σ).obj N)
    { toFun := φ, map_add' := map_add φ, map_smul' := fun r s ↦ map_smulₛₗ φ r s }

/-- A morphism of `R`-modules into the restriction of scalars of `N` along `σ` read as a
`σ`-semilinear map `M ⟶ N`. -/
def ofRestrictScalars (ψ : M ⟶ (ModuleCat.restrictScalars σ).obj N) : M →ₛₗ[σ] N where
  toFun := ψ.hom
  map_add' := map_add ψ.hom
  map_smul' r s := ψ.hom.map_smul r s

/-- Reading a semilinear map into the restriction of scalars and back gives the original map. -/
lemma ofRestrictScalars_toRestrictScalars (φ : M →ₛₗ[σ] N) :
    ofRestrictScalars (toRestrictScalars φ) = φ :=
  rfl

/-- Reading a morphism into the restriction of scalars as a semilinear map and back gives the
original morphism. -/
lemma toRestrictScalars_ofRestrictScalars (ψ : M ⟶ (ModuleCat.restrictScalars σ).obj N) :
    toRestrictScalars (ofRestrictScalars ψ) = ψ :=
  rfl

/-- `toRestrictScalars` is injective. -/
lemma toRestrictScalars_injective {φ ψ : M →ₛₗ[σ] N}
    (h : toRestrictScalars φ = toRestrictScalars ψ) : φ = ψ := by
  rw [← ofRestrictScalars_toRestrictScalars φ, ← ofRestrictScalars_toRestrictScalars ψ, h]

end RestrictScalars

/-- A fan in `AddCommGrpCat` whose projections are the components of an additive equivalence onto
the product type is a limit fan. -/
def isLimitFanOfAddEquiv {ι : Type t} {P : AddCommGrpCat.{m}} {Q : ι → AddCommGrpCat.{m}}
    (π : ∀ i, P ⟶ Q i) (e : P ≃+ (∀ i, Q i)) (he : ∀ (p : P) (i : ι), e p i = π i p) :
    IsLimit (Fan.mk P π) :=
  Fan.IsLimit.mk _
    (fun s ↦ AddCommGrpCat.ofHom
      { toFun := fun w ↦ e.symm (fun i ↦ s.proj i w)
        map_zero' := by
          refine (AddEquiv.map_eq_zero_iff e.symm).2 ?_
          funext i
          exact map_zero (s.proj i).hom
        map_add' := fun a b ↦ by
          rw [← map_add]
          congr 1
          funext i
          exact map_add (s.proj i).hom a b })
    (fun s i ↦ by
      ext w
      exact (he _ i).symm.trans (congrFun (e.apply_symm_apply _) i))
    (fun s n hn ↦ by
      ext w
      refine e.injective (funext fun i ↦ ?_)
      have hr : e (e.symm (fun j ↦ s.proj j w)) i = s.proj i w :=
        congrFun (e.apply_symm_apply _) i
      refine ((he _ i).trans ?_).trans hr.symm
      exact ConcreteCategory.congr_hom (hn i) w)

/-- A fan of homological complexes is a limit fan as soon as it is one in every degree. -/
def isLimitFanOfEval {A : Type*} [Category A] [HasZeroMorphisms A] {ιc : Type*}
    {cs : ComplexShape ιc} {β : Type t} {P : HomologicalComplex A cs}
    {Q : β → HomologicalComplex A cs} (π : ∀ i, P ⟶ Q i)
    (h : ∀ n, IsLimit (Fan.mk (P.X n) (fun i ↦ (π i).f n))) : IsLimit (Fan.mk P π) :=
  HomologicalComplex.isLimitOfEval _ _ fun n ↦
    (Fan.isLimitMapConeEquiv (HomologicalComplex.eval A cs n) Q (Fan.mk P π)).symm (h n)

section Cochains

variable {C : Type u} [SmallCategory C] {O : Cᵒᵖ ⥤ RingCat.{v}}

/-- Acting on a cochain by a morphism of the source module is precomposition with its sections. -/
lemma toRestrictScalars_extCochainMap_fst {G G' F : PresheafOfModules.{m} O} (g : G' ⟶ G)
    (n : ℕ) (φ : extCochain G F n) (x : ComposableArrows C n) :
    toRestrictScalars (extCochainMap g (𝟙 F) n φ x) =
      g.app (op (x.obj (Fin.last n))) ≫ toRestrictScalars (φ x) :=
  rfl

/-- Acting on a cochain by a morphism of the target module is postcomposition with its sections. -/
lemma toRestrictScalars_extCochainMap_snd {G F F' : PresheafOfModules.{m} O} (f : F ⟶ F')
    (n : ℕ) (φ : extCochain G F n) (x : ComposableArrows C n) :
    toRestrictScalars (extCochainMap (𝟙 G) f n φ x) = toRestrictScalars (φ x) ≫
      (ModuleCat.restrictScalars (O.map (stringSpine x).op).hom).map (f.app (op (x.obj 0))) :=
  rfl

/-- The sections over `U` of a direct sum of `O`-modules are the direct sum of the sections. -/
def isColimitEvalCofan {ι : Type t} [Small.{m} ι] {Gι : ι → PresheafOfModules.{m} O}
    (c : Cofan Gι) (hc : IsColimit c) (U : Cᵒᵖ) :
    IsColimit (Cofan.mk (c.pt.obj U) (fun i ↦ (c.inj i).app U)) :=
  Cofan.isColimitMapCoconeEquiv (PresheafOfModules.evaluation O U) Gι c (isColimitOfPreserves _ hc)

/-- The sections over `x.obj 0` of a product of `O`-modules, with scalars restricted along the
spine of `x`, are the product of the restricted sections. -/
def isLimitRestrictScalarsEvalFan {ι : Type t} [Small.{m} ι] {Fι : ι → PresheafOfModules.{m} O}
    (c : Fan Fι) (hc : IsLimit c) {X Y : C} (u : X ⟶ Y) :
    IsLimit (Fan.mk ((ModuleCat.restrictScalars (O.map u.op).hom).obj (c.pt.obj (op X)))
      (fun i ↦ (ModuleCat.restrictScalars (O.map u.op).hom).map ((c.proj i).app (op X)))) :=
  Fan.isLimitMapConeEquiv
    (PresheafOfModules.evaluation O (op X) ⋙ ModuleCat.restrictScalars (O.map u.op).hom) Fι c
    (isLimitOfPreserves _ hc)

/-- The degree-`n` cochains from a direct sum of `O`-modules are the product, over the summands,
of the degree-`n` cochains from the summands. -/
def extCochainCofanAddEquiv {ι : Type t} [Small.{m} ι] {Gι : ι → PresheafOfModules.{m} O}
    (c : Cofan Gι) (hc : IsColimit c) (F : PresheafOfModules.{m} O) (n : ℕ) :
    extCochain c.pt F n ≃+ (∀ i, extCochain (Gι i) F n) where
  toFun φ i := extCochainMap (c.inj i) (𝟙 F) n φ
  invFun ψ x := ofRestrictScalars
    (Cofan.IsColimit.desc (isColimitEvalCofan c hc (op (x.obj (Fin.last n))))
      fun i ↦ toRestrictScalars (ψ i x))
  left_inv φ := by
    funext x
    refine toRestrictScalars_injective ((toRestrictScalars_ofRestrictScalars _).trans ?_)
    refine Cofan.IsColimit.hom_ext (isColimitEvalCofan c hc (op (x.obj (Fin.last n)))) _ _
      fun i ↦ ?_
    exact (Cofan.IsColimit.fac _ _ i).trans (toRestrictScalars_extCochainMap_fst (c.inj i) n φ x)
  right_inv ψ := by
    funext i x
    refine toRestrictScalars_injective
      ((toRestrictScalars_extCochainMap_fst (c.inj i) n _ x).trans ?_)
    exact Cofan.IsColimit.fac (isColimitEvalCofan c hc (op (x.obj (Fin.last n)))) _ i
  map_add' φ ψ := funext fun i ↦ map_add (extCochainMap (c.inj i) (𝟙 F) n) φ ψ

/-- The degree-`n` cochains into a product of `O`-modules are the product, over the factors, of
the degree-`n` cochains into the factors. -/
def extCochainFanAddEquiv {ι : Type t} [Small.{m} ι] {Fι : ι → PresheafOfModules.{m} O}
    (G : PresheafOfModules.{m} O) (c : Fan Fι) (hc : IsLimit c) (n : ℕ) :
    extCochain G c.pt n ≃+ (∀ i, extCochain G (Fι i) n) where
  toFun φ i := extCochainMap (𝟙 G) (c.proj i) n φ
  invFun ψ x := ofRestrictScalars
    (Fan.IsLimit.lift (isLimitRestrictScalarsEvalFan c hc (stringSpine x))
      fun i ↦ toRestrictScalars (ψ i x))
  left_inv φ := by
    funext x
    refine toRestrictScalars_injective ((toRestrictScalars_ofRestrictScalars _).trans ?_)
    refine Fan.IsLimit.hom_ext (isLimitRestrictScalarsEvalFan c hc (stringSpine x)) _ _ fun i ↦ ?_
    exact (Fan.IsLimit.fac _ _ i).trans (toRestrictScalars_extCochainMap_snd (c.proj i) n φ x)
  right_inv ψ := by
    funext i x
    refine toRestrictScalars_injective
      ((toRestrictScalars_extCochainMap_snd (c.proj i) n _ x).trans ?_)
    exact Fan.IsLimit.fac (isLimitRestrictScalarsEvalFan c hc (stringSpine x)) _ i
  map_add' φ ψ := funext fun i ↦ map_add (extCochainMap (𝟙 G) (c.proj i) n) φ ψ

/-- **Stacks 08S0.** The cochain bifunctor transforms direct sums in the first variable into
products: if the cofan `c` exhibits its point as the direct sum of a family `Gι` of `O`-modules,
then the maps which the bifunctor induces from the inclusions `Gι i ⟶ c.pt` exhibit
`K^•(c.pt, F)` as the product of the complexes `K^•(Gι i, F)`. -/
@[stacks 08S0 "direct sums in the first variable become products"]
def isLimitExtCochainComplexFanOfDirectSum {ι : Type t} [Small.{m} ι]
    {Gι : ι → PresheafOfModules.{m} O} (c : Cofan Gι) (hc : IsColimit c)
    (F : PresheafOfModules.{m} O) :
    IsLimit (Fan.mk (f := fun i ↦ extCochainComplex (Gι i) F) (extCochainComplex c.pt F)
      (fun i ↦ (extCochainComplexBifunctor C O).map ((c.inj i).op, 𝟙 F))) :=
  isLimitFanOfEval _ fun n ↦
    isLimitFanOfAddEquiv _ (extCochainCofanAddEquiv c hc F n) fun _ _ ↦ rfl

/-- **Stacks 08S0.** The cochain bifunctor commutes with products in the second variable: if the
fan `c` exhibits its point as the product of a family `Fι` of `O`-modules, then the maps which
the bifunctor induces from the projections `c.pt ⟶ Fι i` exhibit `K^•(G, c.pt)` as the product of
the complexes `K^•(G, Fι i)`. -/
@[stacks 08S0 "products in the second variable"]
def isLimitExtCochainComplexFanOfProduct {ι : Type t} [Small.{m} ι]
    (G : PresheafOfModules.{m} O) {Fι : ι → PresheafOfModules.{m} O}
    (c : Fan Fι) (hc : IsLimit c) :
    IsLimit (Fan.mk (f := fun i ↦ extCochainComplex G (Fι i)) (extCochainComplex G c.pt)
      (fun i ↦ (extCochainComplexBifunctor C O).map (𝟙 (op G), c.proj i))) :=
  isLimitFanOfEval _ fun n ↦
    isLimitFanOfAddEquiv _ (extCochainFanAddEquiv G c hc n) fun _ _ ↦ rfl

end Cochains

end Stacks.CategoryExt
