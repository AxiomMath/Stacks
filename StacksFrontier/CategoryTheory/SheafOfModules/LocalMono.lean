module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable

/-!
# Monomorphy of a morphism of sheaves of modules is local on the site

Let `R` be a sheaf of rings on a site `(C, J)` and let `a : M ⟶ N` be a morphism of sheaves of
`R`-modules. If every object `U` of `C` admits a covering family `V k ⟶ U` along which the
restrictions `a.over (V k)` are monomorphisms, then `a` is a monomorphism.

## Main results

* `SheafOfModules.injective_app_of_cover`: if the sections map of `a` is injective over the
  members of a covering family of every object, then it is injective over every object.
* `SheafOfModules.mono_of_injective_app_of_cover`: the same hypothesis yields `Mono a`.
* `SheafOfModules.injective_app_of_mono_over`: if `a.over X` is a monomorphism, then the sections
  map of `a` over `X` is injective.
* `SheafOfModules.mono_of_locally_mono` and `SheafOfModules.mono_of_locally_isSplitMono`:
  monomorphy is local, with the hypothesis phrased through the restrictions `a.over` to the
  localised sites.
-/

@[expose] public section

open CategoryTheory Opposite

universe w v v₁ u₁ u

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{v} R}

/-- If every object `U` of `C` carries a covering family `V k ⟶ U` such that the sections map of
`a` over each `V k` is injective, then the sections map of `a` is injective over every object. -/
theorem injective_app_of_cover (a : M ⟶ N)
    (ha : ∀ U : C, ∃ (I : Type w) (V : I → C) (f : ∀ k, V k ⟶ U),
      Sieve.ofArrows V f ∈ J U ∧ ∀ k, Function.Injective (a.val.app (op (V k))))
    (X : Cᵒᵖ) : Function.Injective (a.val.app X) := by
  obtain ⟨U⟩ := X
  intro x y hxy
  obtain ⟨I, V, f, hcov, hinj⟩ := ha U
  refine M.isSheaf.isSeparated U _ hcov x y fun W g hg => ?_
  obtain ⟨k, b, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hg
  have key : M.val.map (f k).op x = M.val.map (f k).op y :=
    hinj k (by rw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply, hxy])
  show M.val.map (b ≫ f k).op x = M.val.map (b ≫ f k).op y
  rw [op_comp, PresheafOfModules.map_comp_apply, PresheafOfModules.map_comp_apply, key]

/-- A morphism of sheaves of modules whose sections map is injective over the members of a
covering family of every object is a monomorphism. -/
theorem mono_of_injective_app_of_cover (a : M ⟶ N)
    (ha : ∀ U : C, ∃ (I : Type w) (V : I → C) (f : ∀ k, V k ⟶ U),
      Sieve.ofArrows V f ∈ J U ∧ ∀ k, Function.Injective (a.val.app (op (V k)))) :
    Mono a :=
  (forget R).mono_of_mono_map
    (PresheafOfModules.mono_of_injective (f := a.val) fun {X} => injective_app_of_cover a ha X)

/-- A morphism of sheaves of modules whose restriction to the site localised at `X` is a
monomorphism is injective on the sections over `X`. -/
theorem injective_app_of_mono_over (a : M ⟶ N) (X : C) [Mono (a.over X)] :
    Function.Injective (a.val.app (op X)) :=
  (ModuleCat.mono_iff_injective _).1
    (inferInstanceAs (Mono ((evaluation (R.over X) (op (Over.mk (𝟙 X)))).map (a.over X))))

/-- If every object `U` of `C` carries a covering family `V k ⟶ U` such that the restriction of `a`
to the site localised at each `V k` is a monomorphism, then `a` is a monomorphism. -/
theorem mono_of_locally_mono (a : M ⟶ N)
    (ha : ∀ U : C, ∃ (I : Type w) (V : I → C) (f : ∀ k, V k ⟶ U),
      Sieve.ofArrows V f ∈ J U ∧ ∀ k, Mono (a.over (V k))) :
    Mono a :=
  mono_of_injective_app_of_cover a fun U =>
    let ⟨I, V, f, hcov, h⟩ := ha U
    ⟨I, V, f, hcov, fun k => have := h k; injective_app_of_mono_over a (V k)⟩

/-- If every object `U` of `C` carries a covering family `V k ⟶ U` such that the restriction of `a`
to the site localised at each `V k` is a split monomorphism, then `a` is a monomorphism. -/
theorem mono_of_locally_isSplitMono (a : M ⟶ N)
    (ha : ∀ U : C, ∃ (I : Type w) (V : I → C) (f : ∀ k, V k ⟶ U),
      Sieve.ofArrows V f ∈ J U ∧ ∀ k, IsSplitMono (a.over (V k))) :
    Mono a :=
  mono_of_locally_mono a fun U =>
    let ⟨I, V, f, hcov, h⟩ := ha U
    ⟨I, V, f, hcov, fun k => (h k).mono⟩

end SheafOfModules

end
