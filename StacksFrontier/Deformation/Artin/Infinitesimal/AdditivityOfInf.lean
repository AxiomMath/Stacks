module

public import StacksFrontier.Deformation.Artin.Infinitesimal.Functoriality

/-!
# The addition of `Inf_x(M)` is composition of infinitesimal automorphisms

Let `𝒳` be a category fibred in groupoids over the big fppf site of a scheme `S` satisfying
condition (RS*), let `A` be an `S`-algebra and `x` an object of `𝒳` over `Spec A`.  Stacks
07Y9 makes the infinitesimal automorphisms `Inf_x(M)` of the trivial deformation of `x` over
`A[M]` into an `A`-module, functorially in the `A`-module `M`; that is the content of
`Deformation.Artin.InfinitesimalAutomorphismFunctorData`, whose `autEquiv` field identifies
the underlying set of the module with the set of those automorphisms.

Nothing in that structure says, on the face of it, that the *addition* of the module is the
*composition* of automorphisms.  This file proves that it is, for any such structure — which
is what lets a statement about the module (a difference of two maps, a kernel) be read as a
statement about automorphisms (a quotient of two maps, a conjugation relation).  It is the
counterpart on the Artin-axioms side of Formal Deformation Theory, Lemma 90.11.5 (Tag 06I7).

The argument is the one of the source.  Restriction of endomorphisms along an arrow of a
category fibred in groupoids is a homomorphism of automorphism monoids
(`Deformation.Artin.fiberEndRestrict_comp_end`), so each transition map of `Inf_x` is one.  By
(RS*) the restriction to the two factors is injective on the infinitesimal automorphisms over
`A[M × M]` (`Deformation.Artin.infinitesimalAutomorphismSetFunctor_product_bijective`); the
element with coordinates `(ξ₁, ξ₂)` is therefore the composite of the images of `ξ₁` and `ξ₂`
under the two inclusions, and applying the transition map of the *sum* of the two projections
to it gives `ξ₁ ∘ ξ₂`.  Since the module addition is the transition map of that same sum, the
two agree.

## Main definitions

* `Deformation.Artin.infAutRestrict`: the transition map of the infinitesimal automorphisms
  along a module map, named at the spelling in which its source and target are automorphism
  sets rather than values of a functor to `Type`.  All of the algebra below is done at this
  spelling; `Deformation.Artin.infAutSetFunctor_map_eq'` is the bridge to the functor.

## Main results

* `Deformation.Artin.fiberEndRestrict_comp_end`, `Deformation.Artin.fiberEndRestrict_one`:
  restriction of endomorphisms is a homomorphism of automorphism monoids.
* `Deformation.Artin.infAutRestrict_comp`, `Deformation.Artin.infAutRestrict_one`,
  `Deformation.Artin.infAutRestrict_trans`, `Deformation.Artin.infAutRestrict_id`,
  `Deformation.Artin.infAutRestrict_zero`: the transition maps are functorial homomorphisms of
  automorphism monoids, and the one attached to a zero module map is trivial.
* `Deformation.Artin.infAutRestrict_sum`: **where (RS*) enters** — the transition map along
  the sum of the two projections of `M × M` is the composite of the two.
* `Deformation.Artin.autEquiv_add`: **the addition of `Inf_x(M)` is composition**.
* `Deformation.Artin.autEquiv_neg_comp`, `Deformation.Artin.autEquiv_comp_neg`,
  `Deformation.Artin.autEquiv_sub_comp`: consequently the negation is the inverse automorphism
  and a difference is a quotient.

## References

* [Stacks Project, Tag 06I7](https://stacks.math.columbia.edu/tag/06I7)
* [Stacks Project, Tag 07Y9](https://stacks.math.columbia.edu/tag/07Y9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Deformation.Artin

/-! ### Restriction of endomorphisms is a homomorphism of automorphism monoids -/

section FiberEndHom
open Functor
universe u₁ v₁ u₂ v₂

variable {C : Type u₁} [Category.{v₁} C] {Y : Type u₂} [Category.{v₂} Y]
  (q : Y ⥤ C) (hq : q.IsFiberedInGroupoids)

include hq in
/-- Restriction of endomorphisms along an arrow is multiplicative. -/
public theorem fiberEndRestrict_comp_end {U V : C} {g : V ⟶ U} {a : q.Fiber U} {b : q.Fiber V}
    (φ : b.1 ⟶ a.1) (hφ : q.IsHomLift g φ) (θ θ' : a ⟶ a) :
    fiberEndRestrict q hq φ hφ (θ ≫ θ') =
      fiberEndRestrict q hq φ hφ θ ≫ fiberEndRestrict q hq φ hφ θ' := by
  refine (fiberEndRestrict_eq q hq φ hφ (θ ≫ θ') _ ?_).symm
  have e1 : (fiberEndRestrict q hq φ hφ θ).1 ≫ φ = φ ≫ θ.1 :=
    fiberEndRestrict_fac q hq φ hφ θ
  have e2 : (fiberEndRestrict q hq φ hφ θ').1 ≫ φ = φ ≫ θ'.1 :=
    fiberEndRestrict_fac q hq φ hφ θ'
  change ((fiberEndRestrict q hq φ hφ θ).1 ≫ (fiberEndRestrict q hq φ hφ θ').1) ≫ φ =
    φ ≫ (θ.1 ≫ θ'.1)
  rw [Category.assoc, e2, ← Category.assoc (fiberEndRestrict q hq φ hφ θ).1 φ θ'.1, e1,
    Category.assoc]

include hq in
/-- Restriction of endomorphisms along an arrow preserves the identity. -/
public theorem fiberEndRestrict_one {U V : C} {g : V ⟶ U} {a : q.Fiber U} {b : q.Fiber V}
    (φ : b.1 ⟶ a.1) (hφ : q.IsHomLift g φ) :
    fiberEndRestrict q hq φ hφ (𝟙 a) = 𝟙 b := by
  refine (fiberEndRestrict_eq q hq φ hφ (𝟙 a) (𝟙 b) ?_).symm
  change 𝟙 b.1 ≫ φ = φ ≫ 𝟙 a.1
  rw [Category.id_comp, Category.comp_id]

end FiberEndHom

/-! ### The transition maps of `Inf_x`, as maps of automorphism sets -/

section Restrict
open Functor
universe u v w

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (S : Scheme.{u})
  (hS : B.Contains S) (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
variable {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x : X)
  (hx : p.obj x = algebraOver A B S hS toS hA) (hp : p.IsFiberedInGroupoids)

/-- **The transition map of the infinitesimal automorphisms along a module map**, named at
the spelling in which its source and target are the automorphism sets of the two trivial
deformations: restriction of endomorphisms along the transition arrow. -/
public def infAutRestrict {M N : SiteModule A B} (f : M ⟶ N)
    (θ : trivialDeformation A B S hS toS hA p x hx hp M ⟶
      trivialDeformation A B S hS toS hA p x hx hp M) :
    trivialDeformation A B S hS toS hA p x hx hp N ⟶
      trivialDeformation A B S hS toS hA p x hx hp N :=
  fiberEndRestrict (Under.post p) (underPost_isFiberedInGroupoids p hp x)
    (trivialTransitionUnder A B S hS toS hA p x hx hp f)
    (trivialTransitionUnder_isHomLift A B S hS toS hA p x hx hp f) θ

/-- The bridge to the set-valued functor of infinitesimal automorphisms. -/
public theorem infAutSetFunctor_map_eq' {M N : SiteModule A B} (f : M ⟶ N)
    (θ : trivialDeformation A B S hS toS hA p x hx hp M ⟶
      trivialDeformation A B S hS toS hA p x hx hp M) :
    (infinitesimalAutomorphismSetFunctor A B S hS toS hA p x hx hp).map f θ =
      infAutRestrict A B S hS toS hA p x hx hp f θ :=
  infAutSetFunctor_map_eq A B S hS toS hA p x hx hp f θ

/-- The transition maps are multiplicative. -/
public theorem infAutRestrict_comp {M N : SiteModule A B} (f : M ⟶ N)
    (θ θ' : trivialDeformation A B S hS toS hA p x hx hp M ⟶
      trivialDeformation A B S hS toS hA p x hx hp M) :
    infAutRestrict A B S hS toS hA p x hx hp f (θ ≫ θ') =
      infAutRestrict A B S hS toS hA p x hx hp f θ ≫
        infAutRestrict A B S hS toS hA p x hx hp f θ' :=
  fiberEndRestrict_comp_end (Under.post p) (underPost_isFiberedInGroupoids p hp x)
    (trivialTransitionUnder A B S hS toS hA p x hx hp f)
    (trivialTransitionUnder_isHomLift A B S hS toS hA p x hx hp f) θ θ'

/-- The transition maps preserve the identity automorphism. -/
public theorem infAutRestrict_one {M N : SiteModule A B} (f : M ⟶ N) :
    infAutRestrict A B S hS toS hA p x hx hp f
        (𝟙 (trivialDeformation A B S hS toS hA p x hx hp M)) =
      𝟙 (trivialDeformation A B S hS toS hA p x hx hp N) :=
  fiberEndRestrict_one (Under.post p) (underPost_isFiberedInGroupoids p hp x)
    (trivialTransitionUnder A B S hS toS hA p x hx hp f)
    (trivialTransitionUnder_isHomLift A B S hS toS hA p x hx hp f)

/-- The transition maps compose contravariantly in the module map. -/
public theorem infAutRestrict_trans {M N Q : SiteModule A B} (f : M ⟶ N) (g : N ⟶ Q)
    (θ : trivialDeformation A B S hS toS hA p x hx hp M ⟶
      trivialDeformation A B S hS toS hA p x hx hp M) :
    infAutRestrict A B S hS toS hA p x hx hp (f ≫ g) θ =
      infAutRestrict A B S hS toS hA p x hx hp g
        (infAutRestrict A B S hS toS hA p x hx hp f θ) :=
  (infAutSetFunctor_map_eq' A B S hS toS hA p x hx hp (f ≫ g) θ).symm.trans
    ((Functor.map_comp_apply
        (infinitesimalAutomorphismSetFunctor A B S hS toS hA p x hx hp) f g θ).trans
      ((infAutSetFunctor_map_eq' A B S hS toS hA p x hx hp g _).trans
        (congrArg (infAutRestrict A B S hS toS hA p x hx hp g)
          (infAutSetFunctor_map_eq' A B S hS toS hA p x hx hp f θ))))

/-- The transition map along an identity is the identity. -/
public theorem infAutRestrict_id {M : SiteModule A B}
    (θ : trivialDeformation A B S hS toS hA p x hx hp M ⟶
      trivialDeformation A B S hS toS hA p x hx hp M) :
    infAutRestrict A B S hS toS hA p x hx hp (𝟙 M) θ = θ :=
  (infAutSetFunctor_map_eq' A B S hS toS hA p x hx hp (𝟙 M) θ).symm.trans
    (Functor.map_id_apply
      (infinitesimalAutomorphismSetFunctor A B S hS toS hA p x hx hp) M θ)

/-- **The transition map along a zero module map is trivial**, for a zero map between any two
modules: it factors through the zero endomorphism of the source. -/
public theorem infAutRestrict_zero {M N : SiteModule A B}
    (θ : trivialDeformation A B S hS toS hA p x hx hp M ⟶
      trivialDeformation A B S hS toS hA p x hx hp M) :
    infAutRestrict A B S hS toS hA p x hx hp (0 : M ⟶ N) θ =
      𝟙 (trivialDeformation A B S hS toS hA p x hx hp N) := by
  have hendo : infAutRestrict A B S hS toS hA p x hx hp (0 : M ⟶ M) θ =
      𝟙 (trivialDeformation A B S hS toS hA p x hx hp M) :=
    (infAutSetFunctor_map_eq' A B S hS toS hA p x hx hp (0 : M ⟶ M) θ).symm.trans
      (infinitesimalAutomorphismSetFunctor_map_zero A B S hS toS hA p x hx hp M θ)
  have hsplit : infAutRestrict A B S hS toS hA p x hx hp (0 : M ⟶ N) θ =
      infAutRestrict A B S hS toS hA p x hx hp ((0 : M ⟶ M) ≫ (0 : M ⟶ N)) θ :=
    congrArg (fun g => infAutRestrict A B S hS toS hA p x hx hp g θ) (zero_comp).symm
  rw [hsplit, infAutRestrict_trans, hendo, infAutRestrict_one]

variable (hRS : SatisfiesRSStar B S hS p hp)

include hRS in
/-- **Where (RS*) enters.** An infinitesimal automorphism over `A[M × N]` is determined by its
two restrictions. -/
public theorem infAutRestrict_prod_injective (M N : SiteModule A B) :
    Function.Injective (fun θ : trivialDeformation A B S hS toS hA p x hx hp
          (siteModuleProd A B hA M N) ⟶
        trivialDeformation A B S hS toS hA p x hx hp (siteModuleProd A B hA M N) =>
      (infAutRestrict A B S hS toS hA p x hx hp (siteModuleFst A B hA M N) θ,
        infAutRestrict A B S hS toS hA p x hx hp (siteModuleSnd A B hA M N) θ)) := by
  intro θ θ' h
  refine (infinitesimalAutomorphismSetFunctor_product_bijective A B S hS toS hA p x hx hp
    hRS M N).1 (Prod.ext ?_ ?_)
  · exact (infAutSetFunctor_map_eq' A B S hS toS hA p x hx hp
      (siteModuleFst A B hA M N) θ).trans ((congrArg Prod.fst h).trans
        (infAutSetFunctor_map_eq' A B S hS toS hA p x hx hp
          (siteModuleFst A B hA M N) θ').symm)
  · exact (infAutSetFunctor_map_eq' A B S hS toS hA p x hx hp
      (siteModuleSnd A B hA M N) θ).trans ((congrArg Prod.snd h).trans
        (infAutSetFunctor_map_eq' A B S hS toS hA p x hx hp
          (siteModuleSnd A B hA M N) θ').symm)

/-- The first inclusion followed by the sum of the two projections is the identity. -/
private theorem siteModuleInl_comp_fst_add_snd (M : SiteModule A B) :
    siteModuleInl A B hA M M ≫ (siteModuleFst A B hA M M + siteModuleSnd A B hA M M) = 𝟙 M := by
  rw [Preadditive.comp_add, siteModuleInl_comp_fst, siteModuleInl_comp_snd, add_zero]

/-- The second inclusion followed by the sum of the two projections is the identity. -/
private theorem siteModuleInr_comp_fst_add_snd (M : SiteModule A B) :
    siteModuleInr A B hA M M ≫ (siteModuleFst A B hA M M + siteModuleSnd A B hA M M) = 𝟙 M := by
  rw [Preadditive.comp_add, siteModuleInr_comp_fst, siteModuleInr_comp_snd, zero_add]

include hRS in
/-- **The transition map along the sum of the two projections of `M × M` is the composite of
the transition maps along the two projections.** -/
public theorem infAutRestrict_sum (M : SiteModule A B)
    (ξ : trivialDeformation A B S hS toS hA p x hx hp (siteModuleProd A B hA M M) ⟶
      trivialDeformation A B S hS toS hA p x hx hp (siteModuleProd A B hA M M)) :
    infAutRestrict A B S hS toS hA p x hx hp
        (siteModuleFst A B hA M M + siteModuleSnd A B hA M M) ξ =
      infAutRestrict A B S hS toS hA p x hx hp (siteModuleFst A B hA M M) ξ ≫
        infAutRestrict A B S hS toS hA p x hx hp (siteModuleSnd A B hA M M) ξ := by
  have hcomp : ∀ g : siteModuleProd A B hA M M ⟶ M,
      infAutRestrict A B S hS toS hA p x hx hp g
          (infAutRestrict A B S hS toS hA p x hx hp (siteModuleInl A B hA M M)
              (infAutRestrict A B S hS toS hA p x hx hp (siteModuleFst A B hA M M) ξ) ≫
            infAutRestrict A B S hS toS hA p x hx hp (siteModuleInr A B hA M M)
              (infAutRestrict A B S hS toS hA p x hx hp (siteModuleSnd A B hA M M) ξ)) =
        infAutRestrict A B S hS toS hA p x hx hp (siteModuleInl A B hA M M ≫ g)
            (infAutRestrict A B S hS toS hA p x hx hp (siteModuleFst A B hA M M) ξ) ≫
          infAutRestrict A B S hS toS hA p x hx hp (siteModuleInr A B hA M M ≫ g)
            (infAutRestrict A B S hS toS hA p x hx hp (siteModuleSnd A B hA M M) ξ) := by
    intro g
    rw [infAutRestrict_comp, infAutRestrict_trans, infAutRestrict_trans]
  have hz : infAutRestrict A B S hS toS hA p x hx hp (siteModuleInl A B hA M M)
        (infAutRestrict A B S hS toS hA p x hx hp (siteModuleFst A B hA M M) ξ) ≫
      infAutRestrict A B S hS toS hA p x hx hp (siteModuleInr A B hA M M)
        (infAutRestrict A B S hS toS hA p x hx hp (siteModuleSnd A B hA M M) ξ) = ξ := by
    refine infAutRestrict_prod_injective A B S hS toS hA p x hx hp hRS M M (Prod.ext ?_ ?_)
    · dsimp only
      rw [hcomp, siteModuleInl_comp_fst, siteModuleInr_comp_fst, infAutRestrict_id,
        infAutRestrict_zero, Category.comp_id]
    · dsimp only
      rw [hcomp, siteModuleInl_comp_snd, siteModuleInr_comp_snd, infAutRestrict_zero,
        infAutRestrict_id, Category.id_comp]
  refine (congrArg _ hz.symm).trans ?_
  rw [hcomp, siteModuleInl_comp_fst_add_snd, siteModuleInr_comp_fst_add_snd,
    infAutRestrict_id, infAutRestrict_id]

variable (Inf : InfinitesimalAutomorphismFunctorData A B S hS toS hA p x hx hp)

/-- The defining bijection of `Inf_x` is natural, read at the spelling of
`Deformation.Artin.infAutRestrict`. -/
public theorem autEquiv_natural' {M N : SiteModule A B} (f : M ⟶ N) (u : Inf.functor.obj M) :
    Inf.autEquiv N (Inf.functor.map f u) =
      infAutRestrict A B S hS toS hA p x hx hp f (Inf.autEquiv M u) :=
  (Inf.autEquiv_natural f u).trans
    (infAutSetFunctor_map_eq' A B S hS toS hA p x hx hp f (Inf.autEquiv M u))

include hRS in
/-- **The addition of `Inf_x(M)` is composition of infinitesimal automorphisms.**  This is the
Artin-axioms counterpart of Tag 06I7, and it is what lets a difference of two maps into
`Inf_x(M)` be read as a conjugation relation between automorphisms. -/
public theorem autEquiv_add (M : SiteModule A B) (u v : Inf.functor.obj M) :
    Inf.autEquiv M (u + v) = Inf.autEquiv M u ≫ Inf.autEquiv M v := by
  have hmc : ∀ {M₁ M₂ M₃ : SiteModule A B} (g : M₁ ⟶ M₂) (h : M₂ ⟶ M₃) (t : Inf.functor.obj M₁),
      Inf.functor.map (g ≫ h) t = Inf.functor.map h (Inf.functor.map g t) := by
    intro M₁ M₂ M₃ g h t
    rw [Inf.functor.map_comp]
    rfl
  have key : ∀ g : siteModuleProd A B hA M M ⟶ M,
      Inf.functor.map g (Inf.functor.map (siteModuleInl A B hA M M) u +
          Inf.functor.map (siteModuleInr A B hA M M) v) =
        Inf.functor.map (siteModuleInl A B hA M M ≫ g) u +
          Inf.functor.map (siteModuleInr A B hA M M ≫ g) v := by
    intro g
    rw [_root_.map_add, hmc (siteModuleInl A B hA M M) g u,
      hmc (siteModuleInr A B hA M M) g v]
  have hp₁ : Inf.functor.map (siteModuleFst A B hA M M)
      (Inf.functor.map (siteModuleInl A B hA M M) u +
        Inf.functor.map (siteModuleInr A B hA M M) v) = u := by
    rw [key, siteModuleInl_comp_fst, siteModuleInr_comp_fst]
    simp
  have hp₂ : Inf.functor.map (siteModuleSnd A B hA M M)
      (Inf.functor.map (siteModuleInl A B hA M M) u +
        Inf.functor.map (siteModuleInr A B hA M M) v) = v := by
    rw [key, siteModuleInl_comp_snd, siteModuleInr_comp_snd]
    simp
  have hsum : Inf.functor.map (siteModuleFst A B hA M M + siteModuleSnd A B hA M M)
      (Inf.functor.map (siteModuleInl A B hA M M) u +
        Inf.functor.map (siteModuleInr A B hA M M) v) = u + v := by
    rw [key, siteModuleInl_comp_fst_add_snd, siteModuleInr_comp_fst_add_snd]
    simp
  have hdiv := infAutRestrict_sum A B S hS toS hA p x hx hp hRS M
    (Inf.autEquiv (siteModuleProd A B hA M M)
      (Inf.functor.map (siteModuleInl A B hA M M) u +
        Inf.functor.map (siteModuleInr A B hA M M) v))
  rw [← hsum, autEquiv_natural' A B S hS toS hA p x hx hp Inf _ _, hdiv,
    ← autEquiv_natural' A B S hS toS hA p x hx hp Inf (siteModuleFst A B hA M M) _,
    ← autEquiv_natural' A B S hS toS hA p x hx hp Inf (siteModuleSnd A B hA M M) _,
    hp₁, hp₂]

include hRS in
/-- The negation of `Inf_x(M)` is the inverse automorphism. -/
public theorem autEquiv_neg_comp (M : SiteModule A B) (u : Inf.functor.obj M) :
    Inf.autEquiv M u ≫ Inf.autEquiv M (-u) =
      𝟙 (trivialDeformation A B S hS toS hA p x hx hp M) := by
  rw [← autEquiv_add A B S hS toS hA p x hx hp hRS Inf M u (-u), add_neg_cancel,
    autEquiv_zero A B S hS toS hA p x hx hp Inf M]

include hRS in
/-- The negation of `Inf_x(M)` is the inverse automorphism, on the other side. -/
public theorem autEquiv_comp_neg (M : SiteModule A B) (u : Inf.functor.obj M) :
    Inf.autEquiv M (-u) ≫ Inf.autEquiv M u =
      𝟙 (trivialDeformation A B S hS toS hA p x hx hp M) := by
  rw [← autEquiv_add A B S hS toS hA p x hx hp hRS Inf M (-u) u, neg_add_cancel,
    autEquiv_zero A B S hS toS hA p x hx hp Inf M]

include hRS in
/-- **A difference in `Inf_x(M)` is a quotient of automorphisms**: `u - v` is the unique
automorphism whose composite with `autEquiv v` is `autEquiv u`. -/
public theorem autEquiv_sub_comp (M : SiteModule A B) (u v : Inf.functor.obj M) :
    Inf.autEquiv M (u - v) ≫ Inf.autEquiv M v = Inf.autEquiv M u := by
  rw [← autEquiv_add A B S hS toS hA p x hx hp hRS Inf M (u - v) v, sub_add_cancel]

end Restrict

end Deformation.Artin

end
