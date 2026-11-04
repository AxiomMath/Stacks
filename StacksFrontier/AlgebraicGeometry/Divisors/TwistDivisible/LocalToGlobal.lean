module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeGradedModuleFlat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.AlgebraicGeometry.Cohomology.ZeroDimensionalSupport.Vanishing
public import StacksFrontier.AlgebraicGeometry.Modules.ExactStalkCokernel
public import StacksFrontier.AlgebraicGeometry.QuasiAffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.DualStalk

/-!
# A global section recognised from one stalk

Let `f : A ⟶ B` be a morphism of `𝒪_X`-modules which is injective on every stalk and bijective
on every stalk away from one point `y`. Then a global section of `B` whose germ at `y` lies in
the image of `f_y` is the image of a global section of `A`.

The route is the cokernel. Stalkwise injectivity makes `f` a monomorphism
([Stacks, Tag 01AG]), so `0 ⟶ A ⟶ B ⟶ coker f ⟶ 0` is short exact; stalkwise surjectivity away
from `y` makes the stalks of `coker f` vanish there, so its support is contained in `{y}`. A
section of a module is determined by its germs along the support
(`AlgebraicGeometry.injective_suppGermHom`), so the image of `t` in `Γ(coker f, ⊤)` is detected
at `y` alone, and there it vanishes because the germ of `t` comes from `A_y` while the composite
`A ⟶ B ⟶ coker f` is zero. Taking sections over an open is left exact
(`SheafOfModules.exists_of_shortExact_sections`), so `t` lifts.

## Main results

* `Stacks.Divisors.TwistDivisible.mem_range_sectionsMap_of_germ_mem_range`: **the lifting
  criterion** above.
* `Stacks.Divisors.TwistDivisible.mono_of_injective_stalkHom`: a morphism injective on every
  stalk is a monomorphism, at the `stalkHom` spelling of the stalk map.
* `Stacks.Divisors.TwistDivisible.notMem_supp_of_surjective_stalkHom`: the last term of a short
  exact sequence has trivial stalk wherever the first map is surjective on stalks.

## Implementation notes

**Two stalk maps, one function.** The library carries two stalk maps of a morphism of
`𝒪_X`-modules: `AlgebraicGeometry.SheafOfModules.stalkMap`, whose monomorphism criterion is
`mono_iff_injective_stalkMap`, and `Stacks.AlgebraicGeometry.ReflexiveModules.stalkHom`, which
carries the `𝒪_{X,x}`-linearity the rest of this development uses. Both are determined by the
same germ formula and every element of a stalk is a germ, so they are the same function;
`stalkMap_apply_eq_stalkHom` records that once and `mono_of_injective_stalkHom` is the criterion
read through it.

**The cokernel is formed in `AlgebraicGeometry.Scheme.Modules`.** That category and
`SheafOfModules X.ringCatSheaf` have the same objects and morphisms and their additive and
abelian structures are transported by `inferInstanceAs`, so the short complex built from
`cokernel.π` is accepted by the sectionwise left-exactness statement without any comparison
functor.

## References

* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
* [Stacks Project, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.SheafOfModules.SheafHomStalk
open Stacks.AlgebraicGeometry.ReflexiveModules (stalkHom stalkHom_germAt stalkHom_comp)

universe u

namespace Stacks.Divisors.TwistDivisible

variable {X : Scheme.{u}}



/-- **The library's two stalk maps of a morphism of `𝒪_X`-modules are the same function.** Both
send the germ of a section to the germ of its image, and every element of a stalk is a germ. -/
theorem stalkMap_apply_eq_stalkHom {F G : X.Modules} (f : F ⟶ G) (x : X)
    (m : AlgebraicGeometry.SheafOfModules.stalkObj X.ringCatSheaf x F) :
    (AlgebraicGeometry.SheafOfModules.stalkMap X.ringCatSheaf x f).hom m = stalkHom f x m := by
  obtain ⟨W, hxW, t, rfl⟩ := exists_germ_eq F m
  rw [stalkHom_germAt f x W hxW t]
  exact AlgebraicGeometry.SheafOfModules.stalkMap_germ X.ringCatSheaf x f W hxW t

/-- **A morphism of `𝒪_X`-modules injective on every stalk is a monomorphism.** This is
[Stacks, Tag 01AG] read at the `stalkHom` spelling of the stalk map. -/
theorem mono_of_injective_stalkHom {F G : X.Modules} (f : F ⟶ G)
    (h : ∀ x : X, Function.Injective (stalkHom f x)) : Mono f :=
  (AlgebraicGeometry.SheafOfModules.mono_iff_injective_stalkMap
    (O := X.ringCatSheaf) f).mpr fun x a b hab =>
    h x (((stalkMap_apply_eq_stalkHom f x a).symm.trans hab).trans
      (stalkMap_apply_eq_stalkHom f x b))

/-- The stalk map of the zero morphism is zero. -/
theorem stalkHom_zero {F G : X.Modules} (x : X) (m : modStalk F x) :
    stalkHom (0 : F ⟶ G) x m = 0 := by
  obtain ⟨W, hxW, t, rfl⟩ := exists_germ_eq F m
  rw [stalkHom_germAt (0 : F ⟶ G) x W hxW t]
  have h0 : Scheme.Modules.Hom.app (0 : F ⟶ G) W t = 0 := rfl
  rw [h0]
  exact germAt_zero G hxW

/-- **The last term of a short exact sequence has trivial stalk where the first map is
surjective on stalks.** The stalk of the last term is the cokernel of the stalk map of the first
(`Stacks.SheafOfModules.quotientRangeStalkHomEquiv`), and a surjection has trivial cokernel. -/
theorem notMem_supp_of_surjective_stalkHom {S : ShortComplex X.Modules}
    (hS : S.Exact) [Epi S.g] {x : X} (h : Function.Surjective (stalkHom S.f x)) :
    x ∉ _root_.SheafOfModules.supp S.X₃ := by
  have hzero : ∀ a : modStalk S.X₃ x, a = 0 := by
    intro a
    obtain ⟨q, hq⟩ := (Stacks.SheafOfModules.quotientRangeStalkHomEquiv hS x).surjective a
    obtain ⟨m, hm⟩ := Submodule.Quotient.mk_surjective (stalkHom S.f x).range q
    obtain ⟨n, hn⟩ := h m
    have h0 : q = 0 := by
      rw [← hm]
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨n, hn⟩
    rw [← hq, h0, map_zero]
  rintro ⟨a, ha⟩
  exact ha (hzero a)

/-- **A global section whose germ at one point lies in the image lifts.** Let `f : A ⟶ B` be a
morphism of `𝒪_X`-modules which is injective on every stalk and surjective on every stalk away
from a point `y`, and let `t` be a global section of `B` whose germ at `y` lies in the image of
the stalk map of `f` at `y`. Then `t` is the image of a global section of `A`.

The cokernel of `f` is supported in `{y}`, the image of `t` in it has vanishing germ at `y`
because the germ of `t` comes from `A_y`, hence that image vanishes; left exactness of sections
then produces the lift over `⊤`, and a section of a sheaf of modules is determined by its value
over `⊤`. -/
theorem mem_range_sectionsMap_of_germ_mem_range {A B : X.Modules} (f : A ⟶ B) (y : X)
    (hinj : ∀ x : X, Function.Injective (stalkHom f x))
    (hsurj : ∀ x : X, x ≠ y → Function.Surjective (stalkHom f x))
    (t : _root_.SheafOfModules.sections B)
    (hy : germAt B ⊤ y (Opens.mem_top y) (t.eval (op ⊤)) ∈
      LinearMap.range (stalkHom f y)) :
    t ∈ Set.range (_root_.SheafOfModules.sectionsMap f) := by
  classical
  have hmono : Mono f := mono_of_injective_stalkHom f hinj
  have hzero : f ≫ cokernel.π f = 0 := cokernel.condition f
  set S : ShortComplex X.Modules := ShortComplex.mk f (cokernel.π f) hzero with hSdef
  have hex : S.Exact := ShortComplex.exact_cokernel f
  have hSE : S.ShortExact :=
    { exact := hex, mono_f := hmono, epi_g := by exact coequalizer.π_epi }
  have hsupp : ∀ x : X, x ∈ _root_.SheafOfModules.supp S.X₃ → x = y := by
    intro x hx
    by_contra hne
    exact notMem_supp_of_surjective_stalkHom hex (S := S) (hsurj x hne) hx
  have hgy : germAt S.X₃ ⊤ y (Opens.mem_top y)
      (Scheme.Modules.Hom.app S.g ⊤ (t.eval (op ⊤))) = 0 := by
    obtain ⟨a, ha⟩ := hy
    have h1 : stalkHom S.g y (germAt S.X₂ ⊤ y (Opens.mem_top y) (t.eval (op ⊤)))
        = germAt S.X₃ ⊤ y (Opens.mem_top y)
          (Scheme.Modules.Hom.app S.g ⊤ (t.eval (op ⊤))) :=
      stalkHom_germAt S.g y ⊤ (Opens.mem_top y) _
    rw [← h1, ← ha, ← LinearMap.comp_apply, ← stalkHom_comp S.f S.g y, S.zero]
    exact stalkHom_zero y a
  have hσ : Scheme.Modules.Hom.app S.g ⊤ (t.eval (op ⊤)) = 0 := by
    refine injective_suppGermHom S.X₃ ?_
    rw [map_zero]
    funext x
    obtain ⟨x, hx⟩ := x
    obtain rfl := hsupp x hx
    exact hgy
  obtain ⟨a₀, ha₀⟩ := _root_.SheafOfModules.exists_of_shortExact_sections
    (R := X.ringCatSheaf) (T := S) hSE (op ⊤) (t.eval (op ⊤)) hσ
  refine ⟨Stacks.SheafOfModules.sectionsOfTopOfRingSheaf A a₀, ?_⟩
  refine Stacks.SheafOfModules.sections_ext_of_eval_top B ?_
  have h2 : (_root_.SheafOfModules.sectionsMap f
      (Stacks.SheafOfModules.sectionsOfTopOfRingSheaf A a₀)).eval (op ⊤)
      = _root_.SheafOfModules.homSections S.f (op ⊤)
          ((Stacks.SheafOfModules.sectionsOfTopOfRingSheaf A a₀).eval (op ⊤)) := rfl
  exact (h2.trans (congrArg (fun z => _root_.SheafOfModules.homSections S.f (op ⊤) z)
    (Stacks.SheafOfModules.sectionsOfTopOfRingSheaf_eval_top A a₀))).trans ha₀


end Stacks.Divisors.TwistDivisible

end
