module

public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalIdealRestriction
public import StacksFrontier.CategoryTheory.Sites.Modules.FreeAlgebraConormalBaseChange

/-!
# Surjectivity of a base change of polynomial presentations, and of the ideals it compares

Let `u : 𝒜₁ ⟶ 𝒜₂` be a *locally surjective* morphism of sheaves of commutative rings on a site
and let `ℰ` be a presheaf of sets. The base change morphism

`𝒜₁[ℰ] ⟶ 𝒜₂[ℰ]`

of `StacksFrontier.CategoryTheory.Sites.Modules.FreeAlgebraConormalBaseChange`, which is `u` on
coefficients and the identity on the variables, is then locally surjective as well. Writing
`ℐ' = Ker(𝒜₁[ℰ] ⟶ ℬ)` and `ℐ = Ker(𝒜₂[ℰ] ⟶ ℬ)` for the ideals of the two presentations of one
family of generators `α : ℰ ⟶ ℬ`, it follows that `ℐ' ⟶ ℐ` is locally surjective too: a local
section of `𝒜₁[ℰ]` lifting one of `ℐ` lies in `ℐ'` automatically, the restricted presentation
factoring through the base one.

This is the sentence "there is a surjection `ℐ' ⟶ ℐ`" of Step 1 of the proof of
[Stacks 08U8], in the form in which the proof of [Stacks 08UC] uses it: there `𝒜₁ = f⁻¹𝒪_{S'}`
and `𝒜₂ = f⁻¹𝒪_S` for a first order thickening `t : S ⟶ S'`, so that `u` is the inverse image
of `t^♯` and is surjective, `ℬ = 𝒪_X`, and `ℰ` is the sheaf of sets of the source's Step 1.

## Main definitions

* `Stacks.Sites.FreeAlgebra.polynomialBaseChange`: the morphism of *presheaves* of rings
  `𝒜₁(-)[ℰ(-)] ⟶ 𝒜₂(-)[ℰ(-)]` which base change sheafifies, namely `MvPolynomial.map` of `u`
  on sections.

## Main results

* `Stacks.Sites.FreeAlgebra.isLocallySurjective_polynomialBaseChange`: the presheaf-level map
  is locally surjective when `u` is. This is the one computation here: a polynomial over
  `𝒜₂(U)` has finitely many coefficients, each of which lifts on a covering sieve, so the
  sections which lift locally form a subring containing the coefficients and the variables.
* `Stacks.Sites.FreeAlgebra.isLocallySurjective_baseChange`: **`𝒜₁[ℰ] ⟶ 𝒜₂[ℰ]` is locally
  surjective when `u` is**, the implication whose absence
  `StacksFrontier.CategoryTheory.Sites.Modules.FreeAlgebraConormalBaseChange` records.
* `Stacks.Sites.Conormal.mem_restrictedPresentationIdeal_of_baseChange_mem`: a local section of
  `𝒜₁[ℰ]` whose image lies in `ℐ` already lies in `ℐ'`.
* `Stacks.Sites.Conormal.exists_lift_basePresentationIdeal`: **the surjection `ℐ' ⟶ ℐ`** —
  every local section of `ℐ` is, on a covering sieve, the image of a local section of `ℐ'`.
* `Stacks.Sites.Conormal.IdealRestriction.app_eq_of_baseChange_eq`: a restriction datum for
  `ℐ'` which kills the kernel of `ℐ' ⟶ ℐ` takes the same value on any two lifts of a local
  section of `ℐ`. This is the "induces a well defined map" of the source's Step 1.

## Implementation notes

The subring argument is run as an induction on the polynomial with
`MvPolynomial.induction_on`, on the predicate "the image sieve of this section is covering"
rather than on a subring object: the three closure properties are then exactly that the image
sieve of a sum contains the intersection of the two image sieves, that the image sieve of
`p * X n` contains that of `p`, and that the image sieve of a constant contains the image sieve
of that constant under `u`. The first uses
`CategoryTheory.GrothendieckTopology.intersection_covering` and the other two
`CategoryTheory.GrothendieckTopology.superset_covering`, and no finiteness of the support is
needed anywhere.

Passing from the presheaf-level statement to `baseChange` is the same factorisation argument as
`Stacks.Sites.FreeAlgebra.canonicalPresentation_isLocallySurjective`: base change composed with
the sheafification unit of the source is the presheaf-level map composed with the unit of the
target, both being morphisms out of `𝒜₁(-)[ℰ(-)]` which agree on coefficients and on variables,
and the unit is locally surjective, so
`CategoryTheory.Presheaf.isLocallySurjective_of_isLocallySurjective_fac` applies.

The surjection of ideals is stated as an existence statement over a covering sieve rather than
as local surjectivity of a morphism of presheaves of ideals: `ℐ'` and `ℐ` are objectwise ideals
of the two free algebra sheaves and the library carries no presheaf of ideals for them, and the
covering-sieve form is what a descent along the surjection consumes anyway. The covering sieve
produced is the image sieve of base change itself, so it carries the lift, and membership of
that lift in `ℐ'` is then automatic by
`Stacks.Sites.Conormal.mem_restrictedPresentationIdeal_of_baseChange_mem`.

What is **not** done here is the descent itself: a restriction datum for `ℐ'` which kills the
kernel of `ℐ' ⟶ ℐ` determines a map `ℐ/ℐ² ⟶ 𝒢` only after the locally defined values are glued,
and the gluing is a separate step. `app_eq_of_baseChange_eq` is its well-definedness input.

## References

* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8)
* [Stacks Project, Tag 08UC](https://stacks.math.columbia.edu/tag/08UC)
* [Stacks Project, Tag 08TL](https://stacks.math.columbia.edu/tag/08TL)
-/

@[expose] public section

open CategoryTheory Opposite

universe v u w z

namespace Stacks.Sites.FreeAlgebra

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-! ### The base change morphism before sheafification -/

/-- The morphism of presheaves of commutative rings `𝒜₁(-)[ℰ(-)] ⟶ 𝒜₂(-)[ℰ(-)]` induced by a
morphism `u : 𝒜₁ ⟶ 𝒜₂` of coefficient sheaves: on sections it is `MvPolynomial.map` of `u`,
that is, `u` on coefficients and the identity on the variables. Sheafifying it gives
`Stacks.Sites.FreeAlgebra.baseChange`. -/
noncomputable def polynomialBaseChange {A₁ A₂ : Sheaf J CommRingCat.{w}} (u : A₁ ⟶ A₂)
    (E : Functor Cᵒᵖ (Type w)) :
    polynomialPresheaf J A₁ E ⟶ polynomialPresheaf J A₂ E where
  app U := CommRingCat.ofHom (MvPolynomial.map (u.hom.app U).hom)
  naturality := by
    intro U V f
    apply CommRingCat.hom_ext
    apply MvPolynomial.ringHom_ext
    · intro r
      change MvPolynomial.map (u.hom.app V).hom
          (MvPolynomial.eval₂Hom (MvPolynomial.C.comp (A₁.obj.map f).hom)
            (fun x ↦ MvPolynomial.X (E.map f x)) (MvPolynomial.C r)) =
        MvPolynomial.eval₂Hom (MvPolynomial.C.comp (A₂.obj.map f).hom)
          (fun x ↦ MvPolynomial.X (E.map f x))
          (MvPolynomial.map (u.hom.app U).hom (MvPolynomial.C r))
      have hn := congrArg (fun q : A₁.obj.obj U ⟶ A₂.obj.obj V ↦ q.hom r) (u.hom.naturality f)
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hn
      simp only [MvPolynomial.eval₂Hom_C, RingHom.comp_apply, MvPolynomial.map_C]
      exact congrArg MvPolynomial.C hn
    · intro x
      change MvPolynomial.map (u.hom.app V).hom
          (MvPolynomial.eval₂Hom (MvPolynomial.C.comp (A₁.obj.map f).hom)
            (fun y ↦ MvPolynomial.X (E.map f y)) (MvPolynomial.X x)) =
        MvPolynomial.eval₂Hom (MvPolynomial.C.comp (A₂.obj.map f).hom)
          (fun y ↦ MvPolynomial.X (E.map f y))
          (MvPolynomial.map (u.hom.app U).hom (MvPolynomial.X x))
      rw [MvPolynomial.eval₂Hom_X', MvPolynomial.map_X, MvPolynomial.map_X,
        MvPolynomial.eval₂Hom_X']

/-- The base change morphism of presheaves, read on sections. -/
theorem polynomialBaseChange_app {A₁ A₂ : Sheaf J CommRingCat.{w}} (u : A₁ ⟶ A₂)
    (E : Functor Cᵒᵖ (Type w)) (U : Cᵒᵖ)
    (p : MvPolynomial (E.obj U) (A₁.obj.obj U)) :
    (polynomialBaseChange J u E).app U p = MvPolynomial.map (u.hom.app U).hom p :=
  rfl

/-- Restriction in the presheaf of polynomial rings, read on sections: it is `MvPolynomial`
evaluation, sending a coefficient along the restriction of the coefficient sheaf and a variable
to the restriction of that variable. -/
theorem polynomialPresheaf_map_apply (A : Sheaf J CommRingCat.{w})
    (E : Functor Cᵒᵖ (Type w)) {U V : Cᵒᵖ} (f : U ⟶ V)
    (p : MvPolynomial (E.obj U) (A.obj.obj U)) :
    (polynomialPresheaf J A E).map f p =
      MvPolynomial.eval₂Hom (MvPolynomial.C.comp (A.obj.map f).hom)
        (fun x ↦ MvPolynomial.X (E.map f x)) p :=
  rfl

/-! ### Local surjectivity -/

/-- Membership in the image sieve of the base change morphism of presheaves, with every type
spelled as a polynomial ring rather than as the sections of the presheaf: a morphism `f` of the
site belongs to the image sieve of `p` exactly when the restriction of `p` along `f` is
`MvPolynomial.map` of `u` applied to some polynomial over `𝒜₁`. -/
theorem imageSieve_polynomialBaseChange_iff {A₁ A₂ : Sheaf J CommRingCat.{w}} (u : A₁ ⟶ A₂)
    (E : Functor Cᵒᵖ (Type w)) {U V : C} (f : V ⟶ U)
    (p : MvPolynomial (E.obj (op U)) (A₂.obj.obj (op U))) :
    Presheaf.imageSieve (polynomialBaseChange J u E) p f ↔
      ∃ s : MvPolynomial (E.obj (op V)) (A₁.obj.obj (op V)),
        MvPolynomial.map (u.hom.app (op V)).hom s =
          MvPolynomial.eval₂Hom (MvPolynomial.C.comp (A₂.obj.map f.op).hom)
            (fun x ↦ MvPolynomial.X (E.map f.op x)) p :=
  Iff.rfl

/-- **The image sieve of a polynomial under the base change morphism of presheaves is
covering.**

The polynomials whose image sieve is covering form a subring: the image sieve of a sum contains
the intersection of the two image sieves, that of `p * X n` contains that of `p`, and that of a
constant `C a` contains the image sieve of `a` under `u`, which is covering by hypothesis.
Since that subring contains the coefficients and the variables it is everything, and no
finiteness of the support is used. -/
theorem imageSieve_polynomialBaseChange_mem {A₁ A₂ : Sheaf J CommRingCat.{w}} (u : A₁ ⟶ A₂)
    (E : Functor Cᵒᵖ (Type w)) [Presheaf.IsLocallySurjective J u.hom] {U : C}
    (p : MvPolynomial (E.obj (op U)) (A₂.obj.obj (op U))) :
    Presheaf.imageSieve (polynomialBaseChange J u E) p ∈ J U := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    refine J.superset_covering ?_ (Presheaf.imageSieve_mem J u.hom (U := op U) a)
    rintro V f ⟨r, hr⟩
    refine (imageSieve_polynomialBaseChange_iff J u E f (MvPolynomial.C a)).mpr
      ⟨MvPolynomial.C r, ?_⟩
    rw [MvPolynomial.map_C, MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
    exact congrArg MvPolynomial.C hr
  | add p q hp hq =>
    refine J.superset_covering ?_ (J.intersection_covering hp hq)
    rintro V f ⟨hf, hg⟩
    obtain ⟨s, hs⟩ := (imageSieve_polynomialBaseChange_iff J u E f p).mp hf
    obtain ⟨t, ht⟩ := (imageSieve_polynomialBaseChange_iff J u E f q).mp hg
    refine (imageSieve_polynomialBaseChange_iff J u E f (p + q)).mpr ⟨s + t, ?_⟩
    rw [map_add, map_add, hs, ht]
  | mul_X p n hp =>
    refine J.superset_covering ?_ hp
    rintro V f hf
    obtain ⟨s, hs⟩ := (imageSieve_polynomialBaseChange_iff J u E f p).mp hf
    refine (imageSieve_polynomialBaseChange_iff J u E f (p * MvPolynomial.X n)).mpr
      ⟨s * MvPolynomial.X (E.map f.op n), ?_⟩
    rw [map_mul, map_mul, hs, MvPolynomial.map_X, MvPolynomial.eval₂Hom_X']

/-- **The base change morphism of presheaves is locally surjective when `u` is.** -/
instance isLocallySurjective_polynomialBaseChange {A₁ A₂ : Sheaf J CommRingCat.{w}}
    (u : A₁ ⟶ A₂)
    (E : Functor Cᵒᵖ (Type w)) [Presheaf.IsLocallySurjective J u.hom] :
    Presheaf.IsLocallySurjective J (polynomialBaseChange J u E) where
  imageSieve_mem p := imageSieve_polynomialBaseChange_mem J u E p

/-- Base change composed with the sheafification unit of the source is the presheaf-level base
change composed with the sheafification unit of the target. Both sides are morphisms out of
`𝒜₁(-)[ℰ(-)]` which agree on the coefficients and on the variables. -/
theorem toSheafification_comp_baseChange [HasWeakSheafify J CommRingCat.{w}]
    {A₁ A₂ : Sheaf J CommRingCat.{w}} (u : A₁ ⟶ A₂) (E : Functor Cᵒᵖ (Type w)) :
    (toSheafification J CommRingCat.{w}).app (polynomialPresheaf J A₁ E) ≫
        (sheafToPresheaf J CommRingCat.{w}).map (baseChange J u E) =
      polynomialBaseChange J u E ≫
        (toSheafification J CommRingCat.{w}).app (polynomialPresheaf J A₂ E) := by
  rw [baseChange, freeAlgebraSheafDesc_spec]
  refine NatTrans.ext (funext fun U ↦ ?_)
  apply CommRingCat.hom_ext
  apply MvPolynomial.ringHom_ext
  · intro r
    change MvPolynomial.eval₂Hom _ _ (MvPolynomial.C r) = _
    rw [MvPolynomial.eval₂Hom_C]
    change _ = ((toSheafification J CommRingCat.{w}).app (polynomialPresheaf J A₂ E)).app U
      (MvPolynomial.map (u.hom.app U).hom (MvPolynomial.C r))
    rw [MvPolynomial.map_C]
    rfl
  · intro x
    change MvPolynomial.eval₂Hom _ _ (MvPolynomial.X x) = _
    rw [MvPolynomial.eval₂Hom_X']
    change _ = ((toSheafification J CommRingCat.{w}).app (polynomialPresheaf J A₂ E)).app U
      (MvPolynomial.map (u.hom.app U).hom (MvPolynomial.X x))
    rw [MvPolynomial.map_X]
    rfl

/-- **The base change morphism `𝒜₁[ℰ] ⟶ 𝒜₂[ℰ]` is locally surjective when `u` is.** The
presheaf-level map is locally surjective, the sheafification unit of the target is locally
surjective, and base change factors their composite through the sheafification unit of the
source. -/
instance isLocallySurjective_baseChange [HasWeakSheafify J CommRingCat.{w}]
    [J.WEqualsLocallyBijective CommRingCat.{w}]
    {A₁ A₂ : Sheaf J CommRingCat.{w}} (u : A₁ ⟶ A₂) (E : Functor Cᵒᵖ (Type w))
    [Presheaf.IsLocallySurjective J u.hom] :
    Presheaf.IsLocallySurjective J (baseChange J u E).hom := by
  have h₁ : Presheaf.IsLocallySurjective J (polynomialBaseChange J u E) :=
    isLocallySurjective_polynomialBaseChange J u E
  have h₂ : Presheaf.IsLocallySurjective J
      ((toSheafification J CommRingCat.{w}).app (polynomialPresheaf J A₁ E) ≫
        (sheafToPresheaf J CommRingCat.{w}).map (baseChange J u E)) := by
    rw [toSheafification_comp_baseChange, toSheafification_app]
    have hs : Presheaf.IsLocallySurjective J (toSheafify J (polynomialPresheaf J A₂ E)) :=
      (J.W_toSheafify _).isLocallySurjective
    exact Presheaf.isLocallySurjective_comp J (polynomialBaseChange J u E)
      (toSheafify J (polynomialPresheaf J A₂ E))
  exact Presheaf.isLocallySurjective_of_isLocallySurjective J
    ((toSheafification J CommRingCat.{w}).app (polynomialPresheaf J A₁ E))
    ((sheafToPresheaf J CommRingCat.{w}).map (baseChange J u E))

end Stacks.Sites.FreeAlgebra

namespace Stacks.Sites.Conormal

open Stacks.Sites.FreeAlgebra

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{w}] [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {A₁ A₂ B : Sheaf J CommRingCat.{w}} (u : A₁ ⟶ A₂) (E : Functor Cᵒᵖ (Type w))
  (a₂ : A₂ ⟶ B) (e : E ⟶ underlyingPresheaf J B)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- A local section of `𝒜₁[ℰ]` whose image under base change lies in `ℐ` already lies in `ℐ'`:
the restricted presentation is base change followed by the base presentation, so the section is
killed by the restricted presentation. -/
theorem mem_restrictedPresentationIdeal_of_baseChange_mem (X : Cᵒᵖ)
    (h : (freeAlgebraSheaf J A₁ E).obj.obj X)
    (hh : (baseChange J u E).hom.app X h ∈ basePresentationIdeal J E a₂ e X) :
    h ∈ restrictedPresentationIdeal J u E a₂ e X := by
  have hfac : (baseChange J u E) ≫ (basePresentation J E a₂ e) =
      restrictedPresentation J u E a₂ e := baseChange_comp_desc J u E a₂ e
  rw [RingHom.mem_ker] at hh ⊢
  rw [← hfac]
  exact hh

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The surjection `ℐ' ⟶ ℐ`** of Step 1 of the proof of [Stacks 08U8]. Every local section of
`ℐ` is, on a covering sieve, the image under base change of a local section of `ℐ'`. -/
theorem exists_lift_basePresentationIdeal [J.WEqualsLocallyBijective CommRingCat.{w}]
    [Presheaf.IsLocallySurjective J u.hom] (X : Cᵒᵖ)
    (g : (freeAlgebraSheaf J A₂ E).obj.obj X) (hg : g ∈ basePresentationIdeal J E a₂ e X) :
    ∃ S : Sieve X.unop, S ∈ J X.unop ∧ ∀ ⦃Y : C⦄ (f : Y ⟶ X.unop), S f →
      ∃ h : (freeAlgebraSheaf J A₁ E).obj.obj (op Y),
        h ∈ restrictedPresentationIdeal J u E a₂ e (op Y) ∧
          (baseChange J u E).hom.app (op Y) h =
            ((freeAlgebraSheaf J A₂ E).obj.map f.op) g := by
  have := isLocallySurjective_baseChange J u E
  refine ⟨Presheaf.imageSieve (baseChange J u E).hom g, Presheaf.imageSieve_mem J _ g, ?_⟩
  rintro Y f ⟨h, hh⟩
  exact ⟨h, mem_restrictedPresentationIdeal_of_baseChange_mem J u E a₂ e (op Y) h
    (hh ▸ map_kernel (basePresentation J E a₂ e).hom f.op hg), hh⟩

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **A restriction datum for `ℐ'` which kills the kernel of `ℐ' ⟶ ℐ` takes the same value on
any two lifts.** This is the "induces a well defined `𝒪_X`-linear map `ξ : ℐ/ℐ² ⟶ 𝒢`" of Step 1
of the proof of [Stacks 08U8]: two lifts of one local section of `ℐ` differ by a section killed
by base change, on which the datum vanishes by hypothesis. -/
theorem IdealRestriction.app_eq_of_baseChange_eq
    (G : SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B))
    (ρ : IdealRestriction.{v, u, w, z} (restrictedPresentation J u E a₂ e) G)
    (hρ : ∀ (X : Cᵒᵖ) (h : ↥(restrictedPresentationIdeal J u E a₂ e X)),
      (baseChange J u E).hom.app X (h : (freeAlgebraSheaf J A₁ E).obj.obj X) = 0 →
        ρ.app X h = 0)
    (X : Cᵒᵖ) (h₁ h₂ : ↥(restrictedPresentationIdeal J u E a₂ e X))
    (he : (baseChange J u E).hom.app X (h₁ : (freeAlgebraSheaf J A₁ E).obj.obj X) =
      (baseChange J u E).hom.app X (h₂ : (freeAlgebraSheaf J A₁ E).obj.obj X)) :
    ρ.app X h₁ = ρ.app X h₂ := by
  have hz := hρ X (h₁ - h₂) (by simp [he])
  rw [map_sub] at hz
  exact sub_eq_zero.mp hz

end Stacks.Sites.Conormal

end
