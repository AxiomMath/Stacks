module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.QuotientRestriction
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.QuotientSystemNearVanishingTilde

/-!
# Realizing formal sections on one neighbourhood, from a lifting property of a sections functor

Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A`, let `U = Spec(A) ∖ V(𝔞)` and let `F` be a module
on `U` identified with `M̃|_U`. A formal section of `F` is a compatible family of sections of
`F / IⁿF` on `U`; Stacks 0EIF realizes it as the image of one section of `F` on one open `W ⊆ U`
containing `U ∩ V(I)`.

This file isolates the formal half of that argument. Suppose the sections over `W` of the
modules `Ñ|_U` are computed, naturally in the `A`-module `N`, by a functor `Z` to abelian groups
(in the application `Z(N)` is the module of Čech `1`-cocycles of `N` along generators of an ideal
`J` with `W = U ∖ V(J)`), and suppose that every compatible family of elements of the `Z(M/IⁿM)`
comes from a single element of `Z(M)`. Then every formal section of `F` is realized on `W`. The
argument is a diagram chase: sections of `F / IⁿF` on `U` restrict isomorphically to `W`, where
they are sections of `(M/IⁿM)~|_U` by `Stacks.Algebraization.quotientSystemNearVanishingTildeIso`
and hence elements of `Z(M/IⁿM)`; the lift is an element of `Z(M)`, that is a section of `M̃|_U`,
that is of `F`, on `W`; and comparing reductions modulo `Iⁿ` is comparing images in `Z(M/IⁿM)`.

## Main definitions

* `Stacks.Algebraization.sectionsAtFunctor` — sections over a fixed open, as a functor on modules
  over a scheme.
* `Stacks.Algebraization.formalSectionsToTower` — the map from the inverse system of formal
  sections of `F` to `n ↦ Z(M/IⁿM)`.

## Main results

* `Stacks.Algebraization.exists_comparisonAt_eq_of_surjective_lift` — the realization of every
  formal section on `W`, from the lifting property.

## References

* [Stacks Project, Tag 0EIF](https://stacks.math.columbia.edu/tag/0EIF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

/-- Sections over a fixed open `W`, as a functor from modules on a scheme to abelian groups. -/
abbrev sectionsAtFunctor {X : Scheme.{u}} (W : X.Opens) : X.Modules ⥤ Ab.{u} where
  obj M := Γ(M, W)
  map φ := φ.app W

/-- Restriction of sections from an open to a smaller one, as a natural transformation. -/
abbrev sectionsAtRestriction {X : Scheme.{u}} {W W' : X.Opens} (h : W' ≤ W) :
    sectionsAtFunctor W ⟶ sectionsAtFunctor W' where
  app M := M.presheaf.map (homOfLE h).op
  naturality _ _ φ := (φ.mapPresheaf.naturality (homOfLE h).op).symm

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I a : Ideal A}
  {F : (complementZeroLocus A a : Scheme).Modules} {M : ModuleCat.{u} A}
  (e : F ≅ (Scheme.Modules.restrictFunctor (complementZeroLocus A a).ι).obj
    ((tilde.functor (CommRingCat.of A)).obj M))
  (W : (complementZeroLocus A a : Scheme).Opens)
  (Z : ModuleCat.{u} A ⥤ Ab.{u})
  (Φ : (tilde.functor (CommRingCat.of A) ⋙
      Scheme.Modules.restrictFunctor (complementZeroLocus A a).ι) ⋙ sectionsAtFunctor W ≅ Z)

/-- **The formal sections of `F`, read in `Z`.** At `n`, a section of `F / IⁿF` on `U` is carried
to `(M/IⁿM)~|_U` by `Stacks.Algebraization.quotientSystemNearVanishingTildeIso`, restricted to
`W`, and read in `Z(M/IⁿM)` through `Φ`. -/
def formalSectionsToTower :
    formalSections A I a F ⟶ idealPowerQuotientTower.{u, u} I M ⋙ Z :=
  Functor.whiskerRight (quotientSystemNearVanishingTildeIso e).hom
      (sectionsAtFunctor (⊤ : (complementZeroLocus A a : Scheme).Opens)) ≫
    Functor.whiskerLeft (idealPowerQuotientTower.{u, u} I M ⋙
      tilde.functor (CommRingCat.of A) ⋙
        Scheme.Modules.restrictFunctor (complementZeroLocus A a).ι)
      (sectionsAtRestriction (le_top : W ≤ ⊤)) ≫
    Functor.whiskerLeft (idealPowerQuotientTower.{u, u} I M) Φ.hom

include e Φ in
/-- **Every formal section of `F` is realized on `W`**, provided `W` contains `U ∩ V(I)`, the
sections over `W` of the modules `Ñ|_U` are computed by `Z` naturally in `N`, and every
compatible family of elements of the `Z(M/IⁿM)` comes from one element of `Z(M)`. -/
theorem exists_comparisonAt_eq_of_surjective_lift
    (hW : ∀ x : (complementZeroLocus A a : Scheme), I ≤ x.1.asIdeal → x ∈ W)
    (hlift : Function.Surjective (ConcreteCategory.hom
      (limit.lift (idealPowerQuotientTower.{u, u} I M ⋙ Z)
        (Z.mapCone (idealPowerQuotientCone.{u, u} I M)))))
    (s : ToType (limit (formalSections A I a F))) :
    ∃ (V : OpensNearVanishing A I a) (t : ToType ((sectionsNearVanishing A I a F).obj V)),
      ConcreteCategory.hom (comparisonAt A I a F V) t = s := by
  let V : OpensNearVanishing A I a := ⟨W, hW⟩
  let τ := formalSectionsToTower (I := I) e W Z Φ
  obtain ⟨y, hy⟩ := hlift (ConcreteCategory.hom (limMap τ) s)
  let T := tilde.functor (CommRingCat.of A) ⋙
    Scheme.Modules.restrictFunctor (complementZeroLocus A a).ι
  let β := quotientSystemNearVanishingTildeIso (I := I) e
  let t₀ : ToType ((sectionsAtFunctor W).obj (T.obj M)) := ConcreteCategory.hom (Φ.inv.app M) y
  let t : ToType ((sectionsNearVanishing A I a F).obj V) :=
    ConcreteCategory.hom ((sectionsAtFunctor W).map e.inv) t₀
  refine ⟨V, t, Concrete.limit_ext _ _ _ fun n => ?_⟩
  rw [← ConcreteCategory.comp_apply, comparisonAt_π, ConcreteCategory.comp_apply]
  -- it suffices to compare on `W`, after the restriction isomorphism
  apply (ConcreteCategory.bijective_of_isIso (resNearVanishing A I a F V n)).1
  rw [← ConcreteCategory.comp_apply, IsIso.inv_hom_id, ConcreteCategory.id_apply]
  -- and then after `β` and `Φ`, which are isomorphisms
  apply (ConcreteCategory.bijective_of_isIso ((β.hom.app n).app W)).1
  apply (ConcreteCategory.bijective_of_isIso (Φ.hom.app
    ((idealPowerQuotientTower.{u, u} I M).obj n))).1
  let mk : M ⟶ (idealPowerQuotientTower.{u, u} I M).obj n :=
    ModuleCat.ofHom (I ^ n.unop • (⊤ : Submodule A M)).mkQ
  let pr := (adicProj (idealSheafNearVanishing A I a) F n).app W
  have h1 : pr ≫ (β.hom.app n).app W = (e.hom ≫ T.map mk).app W :=
    congrArg (fun φ => Scheme.Modules.Hom.app φ W)
      (adicProj_quotientSystemNearVanishingTildeIso_hom e n.unop)
  have hL : ConcreteCategory.hom (Φ.hom.app ((idealPowerQuotientTower.{u, u} I M).obj n))
      (ConcreteCategory.hom ((β.hom.app n).app W)
        (ConcreteCategory.hom pr t)) =
      ConcreteCategory.hom (Z.map mk) y := by
    calc _ = ConcreteCategory.hom ((e.inv.app W ≫ pr ≫
            (β.hom.app n).app W) ≫ Φ.hom.app _) t₀ := rfl
      _ = ConcreteCategory.hom ((e.inv ≫ e.hom ≫ T.map mk).app W ≫ Φ.hom.app _) t₀ := by
          rw [h1]; rfl
      _ = ConcreteCategory.hom ((T ⋙ sectionsAtFunctor W).map mk ≫ Φ.hom.app _) t₀ := by
          rw [Iso.inv_hom_id_assoc]; rfl
      _ = ConcreteCategory.hom (Φ.inv.app M ≫ Φ.hom.app M ≫ Z.map mk) y := by
          rw [Φ.hom.naturality]; rfl
      _ = _ := by rw [Iso.inv_hom_id_app_assoc]
  have hR : ConcreteCategory.hom (Φ.hom.app ((idealPowerQuotientTower.{u, u} I M).obj n))
      (ConcreteCategory.hom ((β.hom.app n).app W)
        (ConcreteCategory.hom (resNearVanishing A I a F V n)
          (ConcreteCategory.hom (limit.π (formalSections A I a F) n) s))) =
      ConcreteCategory.hom (τ.app n)
        (ConcreteCategory.hom (limit.π (formalSections A I a F) n) s) := by
    have h2 : resNearVanishing A I a F V n ≫ (β.hom.app n).app W =
        (β.hom.app n).app ⊤ ≫ (sectionsAtRestriction (le_top : W ≤ ⊤)).app _ :=
      ((sectionsAtRestriction (le_top : W ≤ ⊤)).naturality (β.hom.app n)).symm
    calc _ = ConcreteCategory.hom ((resNearVanishing A I a F V n ≫ (β.hom.app n).app W) ≫
          Φ.hom.app _) (ConcreteCategory.hom (limit.π (formalSections A I a F) n) s) := rfl
      _ = _ := by rw [h2]; rfl
  show ConcreteCategory.hom (Φ.hom.app _) (ConcreteCategory.hom ((β.hom.app n).app W)
    (ConcreteCategory.hom pr t)) = _
  rw [hL, hR, ← ConcreteCategory.comp_apply, ← limMap_π, ConcreteCategory.comp_apply, ← hy,
    ← ConcreteCategory.comp_apply, limit.lift_π]
  rfl

end Stacks.Algebraization

end
