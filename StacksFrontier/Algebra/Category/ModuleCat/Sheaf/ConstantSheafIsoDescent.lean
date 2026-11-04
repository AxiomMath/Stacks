module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafFiniteness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafLocalHom

/-!
# An isomorphism of constant sheaves of modules comes from an isomorphism of the modules

Let `(C, J)` be a site whose topos is not empty and let `Λ` be a commutative ring. For a
`Λ`-module `M` write `M̲` for the constant sheaf it generates. The constant sheaf functor is
not full: a morphism `M̲ ⟶ N̲` is only locally of the form `ψ̲`. Nevertheless, when `M` and `N`
are finitely presented, an *isomorphism* `M̲ ≅ N̲` forces an isomorphism `M ≅ N`, and the
isomorphism of modules can be read off on any object of the site that is not sheaf
theoretically empty.

The mechanism is the local description of a morphism of constant sheaves: `ξ` agrees with
`ψ̲` on some covering, its inverse agrees with `χ̲` on a further covering, and over a member of
that covering which is not sheaf theoretically empty the two composites `ψ ≫ χ` and `χ ≫ ψ`
have the same constant sheaf as the identity, hence are the identity, because a module injects
into the sections of its constant sheaf there.

## Main results

* `Stacks.ConstantSheaf.eq_of_constantSheaf_map_app_eq`: the constant sheaf functor is faithful,
  already on the sections over a single object that is not sheaf theoretically empty.
* `Stacks.ConstantSheaf.exists_surjective_of_constantSheaf_iso`: the asymmetric form — an
  isomorphism `M̲ ≅ N̲` with `M` finitely presented is induced by a surjection `M ⟶ N`, with no
  hypothesis on `N`; `Stacks.ConstantSheaf.finite_of_constantSheaf_iso` is the resulting
  transport of finiteness from `M` to `N`.
* `Stacks.ConstantSheaf.nonempty_iso_of_constantSheaf_iso`: **the main result.** An isomorphism
  of the constant sheaves of two finitely presented modules forces an isomorphism of the
  modules.
* `Stacks.ConstantSheaf.exists_surjective_ker_eq_of_constantSheaf_quotient_iso`: if the constant
  sheaf of a quotient `M ⧸ P` is isomorphic to the constant sheaf of `N`, then there is a
  surjection `M ⟶ N` with kernel exactly `P`.

## Implementation notes

The last result is the form in which this is used by the inverse system of a sheaf that is
constant modulo every power of an ideal: the canonical identification of the reduction of `M̲`
modulo a submodule with the constant sheaf of the reduced module gives an isomorphism of
constant sheaves, and what is wanted downstream is a map of modules with a prescribed kernel.
A surjection of constant sheaves does *not* by itself produce one, since the constant sheaf
functor is not full; it is the kernel being the constant sheaf of a submodule that makes the
comparison an isomorphism and so brings the present result into play.

`Stacks.ConstantSheaf.nonempty_iso_of_constantSheaf_iso` asks for no point of the site. The
same conclusion is available through a point, by conjugating the isomorphism with
`CategoryTheory.GrothendieckTopology.Point.constantFiberIso`, which identifies the fibre of a
constant sheaf with its value; non-emptiness of the topos is much weaker than the existence of
a point, and finite presentation of the two modules is what pays for the difference.

Only `Nonempty (M ≅ N)` is asserted, not a distinguished isomorphism: the local description
`Stacks.ConstantSheaf.exists_cover_app_eq_constantSheaf_map` chooses a covering family and a
homomorphism on each of its members, and different members give different homomorphisms.

## References

* [Stacks Project, Tag 093S](https://stacks.math.columbia.edu/tag/093S)
* [Stacks Project, Tag 093N](https://stacks.math.columbia.edu/tag/093N)
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u v w x

namespace Stacks.ConstantSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {Λ : Type w} [CommRing Λ]

section Faithful

variable [HasWeakSheafify J (ModuleCat.{x} Λ)]
  [J.WEqualsLocallyBijective (ModuleCat.{x} Λ)]

/-- The constant sheaf functor is faithful: two homomorphisms whose constant sheaves agree on
the sections over a single object that is not sheaf theoretically empty are equal. -/
theorem eq_of_constantSheaf_map_app_eq {M N : ModuleCat.{x} Λ} (ψ ψ' : M ⟶ N) {U : C}
    (hU : (⊥ : Sieve U) ∉ J U)
    (h : ((constantSheaf J (ModuleCat.{x} Λ)).map ψ).hom.app (op U) =
      ((constantSheaf J (ModuleCat.{x} Λ)).map ψ').hom.app (op U)) :
    ψ = ψ' := by
  refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
  refine injective_constantUnitApp J N hU ?_
  rw [← app_constantUnitApp_map J ψ (op U) m, ← app_constantUnitApp_map J ψ' (op U) m]
  exact congrArg (fun φ => ModuleCat.Hom.hom φ ((constantUnitApp J M (op U)).hom m)) h

end Faithful

section Descent

variable [HasSheafify J (ModuleCat.{x} Λ)]
  [J.WEqualsLocallyBijective (ModuleCat.{x} Λ)]
  [J.HasSheafCompose (forget (ModuleCat.{x} Λ))]

/-- A morphism of constant sheaves agrees with the constant sheaf of a homomorphism on the
sections over some object that is not sheaf theoretically empty and lies over a prescribed one.

This is the local description of a morphism of constant sheaves, with the covering family
replaced by a single well chosen member of it. -/
theorem exists_nonempty_app_eq_constantSheaf_map (M N : ModuleCat.{x} Λ)
    [Module.FinitePresentation Λ (M : Type x)]
    (ξ : (constantSheaf J (ModuleCat.{x} Λ)).obj M ⟶
      (constantSheaf J (ModuleCat.{x} Λ)).obj N) {U : C} (hU : (⊥ : Sieve U) ∉ J U) :
    ∃ (V : C) (_ : V ⟶ U) (ψ : M ⟶ N), (⊥ : Sieve V) ∉ J V ∧
      ∀ (W : C) (_ : W ⟶ V), ξ.hom.app (op W) =
        ((constantSheaf J (ModuleCat.{x} Λ)).map ψ).hom.app (op W) := by
  obtain ⟨I, V, g, hcov, hloc⟩ := exists_cover_app_eq_constantSheaf_map J M N ξ U
  obtain ⟨V₀, f₀, hf₀, hV₀⟩ :=
    Stacks.SheafOfModules.Constant.exists_arrow_with_nonempty_source J _ hcov hU
  obtain ⟨i, a, rfl⟩ := (Sieve.mem_ofArrows_iff V g f₀).mp hf₀
  obtain ⟨ψ, hψ⟩ := hloc i
  exact ⟨V₀, a ≫ g i, ψ, hV₀, fun W p => hψ W (p ≫ a)⟩

/-- **An isomorphism of constant sheaves is induced by a surjection out of the finitely presented
side.** On a site whose topos is not empty, if `M̲ ≅ N̲` and `M` is finitely presented, then some
homomorphism `M ⟶ N` is surjective. Nothing is asked of `N`, so this is the asymmetric form of
`nonempty_iso_of_constantSheaf_iso`: it transports finiteness of `M` to `N`. -/
theorem exists_surjective_of_constantSheaf_iso (hJ : ∃ U : C, (⊥ : Sieve U) ∉ J U)
    (M N : ModuleCat.{x} Λ) [Module.FinitePresentation Λ (M : Type x)]
    (e : (constantSheaf J (ModuleCat.{x} Λ)).obj M ≅
      (constantSheaf J (ModuleCat.{x} Λ)).obj N) :
    ∃ ψ : M ⟶ N, Function.Surjective ψ.hom := by
  obtain ⟨U, hU⟩ := hJ
  obtain ⟨V, -, ψ, hV, hψ⟩ := exists_nonempty_app_eq_constantSheaf_map J M N e.hom hU
  refine ⟨ψ, fun n => ?_⟩
  -- the section of `M̲` over `V` that `e` carries to the canonical section determined by `n`
  have hts : (e.hom.hom.app (op V)).hom
      ((e.inv.hom.app (op V)).hom ((constantUnitApp J N (op V)).hom n)) =
        (constantUnitApp J N (op V)).hom n := by
    show ((e.inv ≫ e.hom).hom.app (op V)).hom _ = _
    rw [e.inv_hom_id]
    rfl
  -- `s` is the canonical section of some `m : M` over an object that is not empty
  obtain ⟨W, p, hp, hW⟩ := Stacks.SheafOfModules.Constant.exists_arrow_with_nonempty_source J _
    (Presheaf.imageSieve_mem J (toSheafify J ((Functor.const Cᵒᵖ).obj M))
      ((e.inv.hom.app (op V)).hom ((constantUnitApp J N (op V)).hom n))) hV
  obtain ⟨m, hm⟩ := hp
  have hm' : (constantUnitApp J M (op W)).hom m =
      (((constantSheaf J (ModuleCat.{x} Λ)).obj M).obj.map p.op).hom
        ((e.inv.hom.app (op V)).hom ((constantUnitApp J N (op V)).hom n)) := hm
  refine ⟨m, injective_constantUnitApp J N hW ?_⟩
  calc (constantUnitApp J N (op W)).hom (ψ.hom m)
      = (((constantSheaf J (ModuleCat.{x} Λ)).map ψ).hom.app (op W)).hom
          ((constantUnitApp J M (op W)).hom m) := (app_constantUnitApp_map J ψ (op W) m).symm
    _ = (e.hom.hom.app (op W)).hom ((constantUnitApp J M (op W)).hom m) := by
          rw [hψ W p]
    _ = (e.hom.hom.app (op W)).hom
          ((((constantSheaf J (ModuleCat.{x} Λ)).obj M).obj.map p.op).hom
            ((e.inv.hom.app (op V)).hom ((constantUnitApp J N (op V)).hom n))) := by rw [hm']
    _ = (((constantSheaf J (ModuleCat.{x} Λ)).obj N).obj.map p.op).hom
          ((e.hom.hom.app (op V)).hom
            ((e.inv.hom.app (op V)).hom ((constantUnitApp J N (op V)).hom n))) :=
          NatTrans.naturality_apply e.hom.hom p.op _
    _ = (constantUnitApp J N (op W)).hom n := by rw [hts, map_constantUnitApp]

/-- Finiteness passes from a finitely presented module to any module with the same constant
sheaf, on a site whose topos is not empty. -/
theorem finite_of_constantSheaf_iso (hJ : ∃ U : C, (⊥ : Sieve U) ∉ J U) (M N : ModuleCat.{x} Λ)
    [Module.Finite Λ (M : Type x)] [Module.FinitePresentation Λ (M : Type x)]
    (e : (constantSheaf J (ModuleCat.{x} Λ)).obj M ≅
      (constantSheaf J (ModuleCat.{x} Λ)).obj N) :
    Module.Finite Λ (N : Type x) :=
  let ⟨ψ, hψ⟩ := exists_surjective_of_constantSheaf_iso J hJ M N e
  Module.Finite.of_surjective ψ.hom hψ

/-- **An isomorphism of constant sheaves of finitely presented modules comes from an
isomorphism of the modules.** On a site whose topos is not empty, two finitely presented
modules with isomorphic constant sheaves are isomorphic. -/
theorem nonempty_iso_of_constantSheaf_iso (hJ : ∃ U : C, (⊥ : Sieve U) ∉ J U)
    (M N : ModuleCat.{x} Λ) [Module.FinitePresentation Λ (M : Type x)]
    [Module.FinitePresentation Λ (N : Type x)]
    (e : (constantSheaf J (ModuleCat.{x} Λ)).obj M ≅
      (constantSheaf J (ModuleCat.{x} Λ)).obj N) :
    Nonempty (M ≅ N) := by
  obtain ⟨U, hU⟩ := hJ
  obtain ⟨V, -, ψ, hV, hψ⟩ := exists_nonempty_app_eq_constantSheaf_map J M N e.hom hU
  obtain ⟨W, q, χ, hW, hχ⟩ := exists_nonempty_app_eq_constantSheaf_map J N M e.inv hV
  have hψW := hψ W q
  have hχW := hχ W (𝟙 W)
  have key : ∀ {A B : ModuleCat.{x} Λ} (θ : A ⟶ B) (θ' : B ⟶ A)
      (ε : (constantSheaf J (ModuleCat.{x} Λ)).obj A ⟶
        (constantSheaf J (ModuleCat.{x} Λ)).obj B)
      (ε' : (constantSheaf J (ModuleCat.{x} Λ)).obj B ⟶
        (constantSheaf J (ModuleCat.{x} Λ)).obj A),
      ε.hom.app (op W) = ((constantSheaf J (ModuleCat.{x} Λ)).map θ).hom.app (op W) →
      ε'.hom.app (op W) = ((constantSheaf J (ModuleCat.{x} Λ)).map θ').hom.app (op W) →
      ε ≫ ε' = 𝟙 _ → θ ≫ θ' = 𝟙 A := by
    intro A B θ θ' ε ε' hε hε' hcomp
    refine eq_of_constantSheaf_map_app_eq J _ _ hW ?_
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
    show ((constantSheaf J (ModuleCat.{x} Λ)).map θ).hom.app (op W) ≫
      ((constantSheaf J (ModuleCat.{x} Λ)).map θ').hom.app (op W) = _
    rw [← hε, ← hε']
    show (ε ≫ ε').hom.app (op W) = _
    rw [hcomp]
  exact ⟨⟨ψ, χ, key ψ χ e.hom e.inv hψW hχW e.hom_inv_id,
    key χ ψ e.inv e.hom hχW hψW e.inv_hom_id⟩⟩

/-- If the constant sheaf of a quotient `M ⧸ P` is isomorphic to the constant sheaf of `N`,
then there is a surjection `M ⟶ N` whose kernel is exactly `P`. -/
theorem exists_surjective_ker_eq_of_constantSheaf_quotient_iso
    (hJ : ∃ U : C, (⊥ : Sieve U) ∉ J U) (M N : ModuleCat.{x} Λ) (P : Submodule Λ (M : Type x))
    [Module.FinitePresentation Λ ((M : Type x) ⧸ P)]
    [Module.FinitePresentation Λ (N : Type x)]
    (e : (constantSheaf J (ModuleCat.{x} Λ)).obj (ModuleCat.of Λ ((M : Type x) ⧸ P)) ≅
      (constantSheaf J (ModuleCat.{x} Λ)).obj N) :
    ∃ ψ : M ⟶ N, Function.Surjective ψ.hom ∧ LinearMap.ker ψ.hom = P := by
  obtain ⟨f⟩ := nonempty_iso_of_constantSheaf_iso J hJ _ N e
  have hbij := ConcreteCategory.bijective_of_isIso f.hom
  refine ⟨ModuleCat.ofHom P.mkQ ≫ f.hom, ?_, ?_⟩
  · simpa using hbij.2.comp P.mkQ_surjective
  · refine Submodule.ext fun m => ?_
    show f.hom.hom (P.mkQ m) = 0 ↔ m ∈ P
    rw [map_eq_zero_iff _ hbij.1, P.mkQ_apply, Submodule.Quotient.mk_eq_zero]

end Descent

end Stacks.ConstantSheaf

end
