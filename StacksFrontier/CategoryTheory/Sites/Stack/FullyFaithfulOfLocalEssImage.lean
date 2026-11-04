module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.PullbackFiberComp
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.FibreFunctor
public import StacksFrontier.CategoryTheory.Sites.Stack.TwoFibreProductMorPresheafMap

/-!
# Full faithfulness of a 1-morphism from a local criterion on fibres

Let `(𝒞, J)` be a site, let `p : A ⥤ 𝒞` and `q : B ⥤ 𝒞` be categories fibred in groupoids over
`𝒞` and let `F : A ⥤ B` be a 1-morphism of fibred categories over `𝒞`. This file proves that `F`
is fully faithful as soon as, for every object `U` of `𝒞` and every pair of objects of the fibre
`A_U`, the map on morphisms induced by `F` is bijective after restriction along the members of
some covering sieve of `U`; and the variant where the local datum is instead that every object of
`A_U` lies, locally on `U`, in the essential image of a fully faithful functor `I : A₀ ⥤ A` whose
composite with `F` is also fully faithful.

Both statements ask of `p` and of `q` only that their morphism presheaves `Mor(x, y)` be sheaves
for the induced topology on `𝒞/U` — condition (2) of Stacks 026F — rather than the full stack
condition. That clause is all the argument consumes: the local bijectivity is spread over a
covering sieve, and the two morphism sheaves turn it into an isomorphism of presheaves on `𝒞/U`
(Stacks 04WQ, via `CategoryTheory.Sheaf.isLocallyBijective_iff_isIso`), whose value at the
identity is the bijectivity of `F` on the fibre `A_U`. Full faithfulness of `F` itself is then
the fibrewise criterion for categories fibred in groupoids,
`CategoryTheory.Functor.IsFiberedInGroupoids.full_and_faithful_iff_forall_fiber`.

Asking only for the morphism sheaves widens the reach of the criterion. Condition (3) of
Stacks 026F for a 2-fibre product,
`CategoryTheory.TwoFibreProductOver.hasEffectiveDescent_structureFunctor`, identifies the hom
universe of the base site with the common hom universe of the three categories of the cospan, so
a 2-fibre product of a quotient stack over a big fppf site, whose categories have their morphisms
one universe above the site's, has no `CategoryTheory.Functor.IsStack` available. Condition (2)
at independent universes is
`CategoryTheory.TwoFibreProductOver.IndependentBase.isMorSheaf_structureFunctor`, and the
criteria below apply there. The same weakening is carried out for the equivalence criterion of
Stacks 046N in
`StacksFrontier/CategoryTheory/Sites/InheritedTopology/EquivalenceOverMorSheafTarget.lean`.

## Main results

* `CategoryTheory.Functor.fullyFaithful_of_locallyBijective_of_isMorSheaf`: a 1-morphism of
  categories fibred in groupoids which is locally bijective on fibre morphisms is fully faithful.
* `CategoryTheory.Functor.fullyFaithful_of_locallyEssImage_of_isMorSheaf`: the variant whose
  local datum is membership in the essential image of a fully faithful `I : A₀ ⥤ A`.
* `CategoryTheory.Functor.isIso_of_bijective_app_on_cover`: a map of sheaves on `𝒞/U` which is
  bijective at every member of a covering sieve of `U` is an isomorphism.
* `CategoryTheory.Functor.bijective_map_of_isoPair`: bijectivity of the action of a functor on a
  hom-set transports along isomorphisms of the source and target.

## References

* [Stacks Project, Tag 003Z](https://stacks.math.columbia.edu/tag/003Z)
* [Stacks Project, Tag 026F](https://stacks.math.columbia.edu/tag/026F)
* [Stacks Project, Tag 04WQ](https://stacks.math.columbia.edu/tag/04WQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Functor

universe u v w u' v' w'

/-- Bijectivity of the action of a functor `F` on a hom-set transports along isomorphisms of the
source and the target: if `F` is bijective on `x' ⟶ y'` and `x ≅ x'`, `y ≅ y'`, then `F` is
bijective on `x ⟶ y`. Conjugating a morphism by the two isomorphisms is a bijection
`(x ⟶ y) ≃ (x' ⟶ y')` compatible with `F.map`. -/
theorem bijective_map_of_isoPair
    {A : Type u} {B : Type v} [Category.{w} A] [Category.{w'} B]
    (F : A ⥤ B) {x y x' y' : A} (ex : x ≅ x') (ey : y ≅ y')
    (h : Function.Bijective (F.map : (x' ⟶ y') → _)) :
    Function.Bijective (F.map : (x ⟶ y) → _) := by
  constructor
  · intro m n hmn
    have he : ex.inv ≫ m ≫ ey.hom = ex.inv ≫ n ≫ ey.hom :=
      h.1 (by simp only [Functor.map_comp, hmn])
    simpa using congrArg (fun a => ex.hom ≫ a ≫ ey.inv) he
  · intro m
    obtain ⟨n, hn⟩ := h.2 (F.map ex.inv ≫ m ≫ F.map ey.hom)
    refine ⟨ex.hom ≫ n ≫ ey.inv, ?_⟩
    simp [hn, ← F.map_comp, Category.assoc]

/-- **A map of sheaves on `𝒞/U` which is bijective at every member of a covering sieve of `U` is
an isomorphism** (Stacks 04WQ).

Bijectivity along a covering sieve `R` makes `φ` locally injective and locally surjective for the
induced topology `J.over U`: any sieve of `𝒞/U` pulled back from `R` is a covering, and on it the
components of `φ` are bijective. A map of sheaves which is locally bijective is an isomorphism,
by `CategoryTheory.Sheaf.isLocallyBijective_iff_isIso`. -/
theorem isIso_of_bijective_app_on_cover
    {D : Type u} [Category.{v} D] (J : GrothendieckTopology D)
    {U : D} {P Q : (Over U)ᵒᵖ ⥤ Type w} (φ : P ⟶ Q)
    (hP : Presheaf.IsSheaf (J.over U) P) (hQ : Presheaf.IsSheaf (J.over U) Q)
    (R : Sieve U) (hR : R ∈ J U)
    (h : ∀ {V} (f : V ⟶ U), R f → Function.Bijective (φ.app (op (Over.mk f)))) :
    IsIso φ := by
  have hi : Presheaf.IsLocallyInjective (J.over U) φ := by
    constructor
    intro X a b hab
    obtain ⟨X⟩ := X
    apply (J.over U).superset_covering _
      (J.overEquiv_symm_mem_over X (R.pullback X.hom) (J.pullback_stable X.hom hR))
    intro Y k hk
    have hk' : R (k.left ≫ X.hom) := (Sieve.overEquiv_symm_iff _ k).1 hk
    have hb := h Y.hom (by simpa using hk')
    apply hb.1
    show φ.app (op Y) (P.map k.op a) = φ.app (op Y) (P.map k.op b)
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hab]
  have hs : Presheaf.IsLocallySurjective (J.over U) φ := by
    constructor
    intro X b
    apply (J.over U).superset_covering _
      (J.overEquiv_symm_mem_over X (R.pullback X.hom) (J.pullback_stable X.hom hR))
    intro Y k hk
    have hk' : R (k.left ≫ X.hom) := (Sieve.overEquiv_symm_iff _ k).1 hk
    exact (h Y.hom (by simpa using hk')).2 (Q.map k.op b)
  let ψ : (⟨P, hP⟩ : Sheaf (J.over U) (Type w)) ⟶ ⟨Q, hQ⟩ := ⟨φ⟩
  have : Sheaf.IsLocallyInjective ψ := hi
  have : Sheaf.IsLocallySurjective ψ := hs
  have : IsIso ψ := (Sheaf.isLocallyBijective_iff_isIso ψ).1 ⟨inferInstance, inferInstance⟩
  exact (sheafToPresheaf (J.over U) (Type w)).map_isIso ψ

/-- **A 1-morphism of categories fibred in groupoids which is locally bijective on morphisms of
fibres is fully faithful.**

The hypotheses `hp'` and `hq'` are condition (2) of Stacks 026F for `p` and for `q`: the
presheaves `Mor(x, y)` on `𝒞/U` are sheaves for the induced topology. For fixed `U` and `x y` in
the fibre `A_U`, the local bijectivity along a covering sieve makes the induced map of morphism
presheaves an isomorphism (`CategoryTheory.Functor.isIso_of_bijective_app_on_cover`, Stacks 04WQ);
evaluating at the identity of `U` gives bijectivity of `F` on the fibre `A_U`, and the fibrewise
criterion for categories fibred in groupoids promotes that to full faithfulness of `F`. -/
theorem fullyFaithful_of_locallyBijective_of_isMorSheaf
    {𝒞 : Type u} [Category.{v} 𝒞]
    {A : Type u'} {B : Type v'} [Category.{w} A] [Category.{w} B]
    {p : A ⥤ 𝒞} {q : B ⥤ 𝒞} [p.IsFibered] [q.IsFibered]
    {F : A ⥤ B} (hF : p.IsFibredOneMorphism q F)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (J : GrothendieckTopology 𝒞)
    (hp' : ∀ (U : 𝒞) (a b : p.Fiber U), IsMorSheaf p J U a b)
    (hq' : ∀ (U : 𝒞) (a b : q.Fiber U), IsMorSheaf q J U a b)
    (hlocal : ∀ U (x y : p.Fiber U), ∃ R ∈ J U, ∀ {V} (f : V ⟶ U), R f →
      Function.Bijective ((fiberFunctorOfCompEq hF.comp_eq V).map :
        (pullbackFiber p x f ⟶ pullbackFiber p y f) → _)) :
    Nonempty F.FullyFaithful := by
  suffices hh : ∀ U, (Fiber.mapOfComp p q F hF.comp_eq U).Full ∧
      (Fiber.mapOfComp p q F hF.comp_eq U).Faithful by
    obtain ⟨hfull, hfaith⟩ :=
      (IsFiberedInGroupoids.full_and_faithful_iff_forall_fiber p q hp hq F hF.comp_eq).2 hh
    exact ⟨FullyFaithful.ofFullyFaithful F⟩
  intro U
  suffices hh : Nonempty (fiberFunctorOfCompEq hF.comp_eq U).FullyFaithful from
    ⟨hh.some.full, hh.some.faithful⟩
  rw [FullyFaithful.nonempty_iff_map_bijective]
  intro x y
  obtain ⟨R, hR, hl⟩ := hlocal U x y
  have hiso : IsIso (hF.morPresheafMap x y) :=
    isIso_of_bijective_app_on_cover J _ (hp' U x y) (hq' U _ _) R hR
      (fun {V} f hf => by
        exact ((hF.mapPullbackFiberIso x f).symm.homCongr
          (hF.mapPullbackFiberIso y f).symm).bijective.comp (hl f hf))
  have hb := (asIso ((hF.morPresheafMap x y).app (op (Over.mk (𝟙 U))))).toEquiv.bijective
  let e := (hF.mapPullbackFiberIso x (𝟙 U)).symm.homCongr
    (hF.mapPullbackFiberIso y (𝟙 U)).symm
  have hh : Function.Bijective ((fiberFunctorOfCompEq hF.comp_eq U).map :
      (pullbackFiber p x (𝟙 U) ⟶ pullbackFiber p y (𝟙 U)) → _) := by
    exact (e.bijective.of_comp_iff' _).1 hb
  exact bijective_map_of_isoPair _ (pullbackFiberIdIso x).symm (pullbackFiberIdIso y).symm hh

/-- **A 1-morphism of categories fibred in groupoids is fully faithful as soon as every object of
every fibre is, locally on the base, in the essential image of a fully faithful `I : A₀ ⥤ A`
whose composite with `F` is fully faithful.**

As above, `hp'` and `hq'` are condition (2) of Stacks 026F for `p` and for `q`. Given `x y` in
the fibre `A_U`, intersect the two covering sieves supplied by `hlocal` for `x` and for `y`; over
a member of the intersection both pullbacks come from `A₀`, where the action of `F` on morphisms
factors as the action of `I` followed by that of `I ⋙ F`, both bijective. Transporting along the
two isomorphisms (`CategoryTheory.Functor.bijective_map_of_isoPair`) gives the local bijectivity
required by `CategoryTheory.Functor.fullyFaithful_of_locallyBijective_of_isMorSheaf`. -/
theorem fullyFaithful_of_locallyEssImage_of_isMorSheaf
    {𝒞 : Type u} [Category.{v} 𝒞]
    {A₀ : Type u'} {A : Type v'} {B : Type w'}
    [Category.{w} A₀] [Category.{w} A] [Category.{w} B]
    {p₀ : A₀ ⥤ 𝒞} {p : A ⥤ 𝒞} {q : B ⥤ 𝒞} [p.IsFibered] [q.IsFibered]
    (I : A₀ ⥤ A) (hI : I ⋙ p = p₀) (hi : I.FullyFaithful)
    {F : A ⥤ B} (hF : p.IsFibredOneMorphism q F) (hIF : (I ⋙ F).FullyFaithful)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (J : GrothendieckTopology 𝒞)
    (hp' : ∀ (U : 𝒞) (a b : p.Fiber U), IsMorSheaf p J U a b)
    (hq' : ∀ (U : 𝒞) (a b : q.Fiber U), IsMorSheaf q J U a b)
    (hlocal : ∀ U (x : p.Fiber U), ∃ R ∈ J U, ∀ {V} (f : V ⟶ U), R f →
      (fiberFunctorOfCompEq hI V).essImage (pullbackFiber p x f)) :
    Nonempty F.FullyFaithful := by
  apply fullyFaithful_of_locallyBijective_of_isMorSheaf hF hp hq J hp' hq'
  intro U x y
  obtain ⟨R, hR, hx⟩ := hlocal U x
  obtain ⟨S, hS, hy⟩ := hlocal U y
  refine ⟨R ⊓ S, J.intersection_covering hR hS, ?_⟩
  intro V f hf
  obtain ⟨a, ⟨ea⟩⟩ := hx f hf.1
  obtain ⟨b, ⟨eb⟩⟩ := hy f hf.2
  let If := fiberFunctorOfCompEq hI V
  let Ff := fiberFunctorOfCompEq hF.comp_eq V
  have : I.Full := hi.full
  have : I.Faithful := hi.faithful
  have : (I ⋙ F).Full := hIF.full
  have : (I ⋙ F).Faithful := hIF.faithful
  have : If.Full := Fiber.full_mapOfComp hI V
  have : If.Faithful := Fiber.faithful_mapOfComp hI V
  have hw : (I ⋙ F) ⋙ q = p₀ := by rw [Functor.assoc, hF.comp_eq, hI]
  have : (If ⋙ Ff).Full := Fiber.full_mapOfComp hw V
  have : (If ⋙ Ff).Faithful := Fiber.faithful_mapOfComp hw V
  apply bijective_map_of_isoPair Ff ea.symm eb.symm
  exact (Function.Bijective.of_comp_iff _
    ((FullyFaithful.ofFullyFaithful If).map_bijective a b)).1
    ((FullyFaithful.ofFullyFaithful (If ⋙ Ff)).map_bijective a b)

end CategoryTheory.Functor
