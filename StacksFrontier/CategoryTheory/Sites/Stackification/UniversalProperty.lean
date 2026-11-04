module

public import StacksFrontier.CategoryTheory.Sites.Stack.TwoFibreProductMorPresheafMap
import StacksCore.Tactic.EgaSgaAttribute

/-! # Extending a map of presheaves along a locally bijective map into a sheaf

Let `(𝒟, K)` be a site and let `φ : P ⟶ Q` be a map of presheaves of types on `𝒟` which is
locally injective and locally surjective — the form in which "`Q` is the sheafification of `P`"
is stated throughout this library, following clause (1) of Stacks 02ZN. Then every map
`ψ : P ⟶ T` into a sheaf `T` factors uniquely through `φ`. This is the universal property of
sheafification, proved directly from the sheaf condition rather than through a sheafification
functor.

Proving it directly is not a matter of taste. Mathlib has the same statement as
`CategoryTheory.GrothendieckTopology.W.homEquiv`, reached from
`CategoryTheory.GrothendieckTopology.W_of_isLocallyBijective`, but that route needs
`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective`, hence a sheafification functor for
the presheaves in question, and for type-valued presheaves Mathlib supplies one only in
`Type (max u v)` for a site with `Type u`-many objects and `Type v`-small hom sets. The presheaves
this file is written for are the presheaves `Mor(x, y)` of Stacks 02ZB on the slice `𝒞/U`, which
are valued in the hom universe of the total category alone, so the sheafification route would
force `UnivLE.{max u₁ v, v}` — the hypothesis the statement of Stacks 02ZN carries and documents
as forced for the *existence* of a stackification. Factoring one map through another needs no
sheafification and no such hypothesis, and this file has none.

The hom universe of the site is independent of the hom universe shared by the three categories
fibred over it, as it is in `IsFibredOneMorphism.morPresheafMap` itself; only the sharing among
those three is forced, by the source and target of that map being presheaves valued in their hom
universes.

The application is the morphism half of the universal property of stackification, Stacks 0435: if
`G : 𝒮 ⥤ 𝒮'` exhibits `𝒮'` as the stackification of `𝒮` and `F : 𝒮 ⥤ 𝒳` is a 1-morphism into a
stack, then for all `x`, `y` in a fibre of `𝒮` the presheaf `Mor(F x, F y)` receives a unique map
from `Mor(G x, G y)` compatible with `F` and `G`: the action that any extension `H : 𝒮' ⥤ 𝒳` of
`F` along `G` must have on morphisms between objects in the image of `G`.

## Main results

* `CategoryTheory.Presheaf.existsUnique_hom_of_isLocallyBijective`: a map into a sheaf factors
  uniquely through a locally injective, locally surjective map;
* `CategoryTheory.Functor.existsUnique_morPresheafMap_fac`: its instance at the morphism
  presheaves of Stacks 02ZB, for a stackification in the sense of clause (1) of Stacks 02ZN;
* `CategoryTheory.Presheaf.isLocallyInjective_whiskerRight_typeUliftFunctor`,
  `CategoryTheory.Presheaf.isLocallySurjective_whiskerRight_typeUliftFunctor` and
  `CategoryTheory.Presheaf.isSheaf_whiskerRight_typeUliftFunctor`: all three hypotheses are
  stable under raising the universe of the values, so the factorisation applies to presheaves
  valued in different universes once each has been raised to their common upper bound. This is
  what lets the extension of Stacks 0435 be built when the hom universes of the total categories
  are independent. The qualifier `type` is the value category: these are the statements for the
  universe lift `CategoryTheory.uliftFunctor` of presheaves of types, as against the abelian
  group versions `CategoryTheory.Presheaf.isLocallyInjective_whiskerRight_uliftFunctor` and
  `isLocallySurjective_whiskerRight_uliftFunctor` for `AddCommGrpCat.uliftFunctor` in
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafIsos`.

## Implementation notes

The factorisation is built in the usual way: a section of `Q` lifts to `P` along the members of a
covering sieve (`CategoryTheory.Presheaf.imageSieve`), the `ψ`-images of the lifts agree on
overlaps because two sections of `P` with the same image under `φ` agree locally and `T` is
separated, and the sheaf condition amalgamates them. It is packaged as
`CategoryTheory.Presheaf.existsUnique_section`, the statement that a section of `Q` over `X` has a
unique value in `T` over `X`, characterised by what it restricts to wherever the given section
lifts. Naturality of the resulting map and both halves of the universal property are then read
off from that characterisation, so the amalgamation is never unfolded twice.

Nothing here carries the tag 0435: the universal property of stackification asserts a 1-morphism
`H : 𝒮' ⥤ 𝒳` and a 2-isomorphism `F ≅ G ⋙ H`, which is more than the action on morphism
presheaves proved here.

## References

* [Stacks 02ZN](https://stacks.math.columbia.edu/tag/02ZN), clause (1);
* [Stacks 0435](https://stacks.math.columbia.edu/tag/0435), whose morphism half this is.
-/

@[expose] public section

namespace CategoryTheory

open Opposite

namespace Presheaf

universe w w' v u

variable {𝒟 : Type u} [Category.{v} 𝒟] {P Q T : 𝒟ᵒᵖ ⥤ Type w}

/-- **Raising the universe of the values of a presheaf preserves local injectivity.** The sections
of `P ⋙ uliftFunctor` are the sections of `P` wrapped in `ULift.up`, which is injective, and the
equalizer sieve of two of them is the equalizer sieve of their underlying sections. -/
instance isLocallyInjective_whiskerRight_typeUliftFunctor (K : GrothendieckTopology 𝒟) (φ : P ⟶ Q)
    [IsLocallyInjective K φ] :
    IsLocallyInjective K (Functor.whiskerRight φ uliftFunctor.{w'}) where
  equalizerSieve_mem x y h := by
    convert equalizerSieve_mem K φ x.down y.down (congrArg ULift.down h) using 1
    ext Y f
    exact ⟨fun hh => congrArg ULift.down hh, fun hh => congrArg ULift.up hh⟩

/-- **Raising the universe of the values of a presheaf preserves local surjectivity.** The image
sieve of a section of `Q ⋙ uliftFunctor` is the image sieve of its underlying section. -/
instance isLocallySurjective_whiskerRight_typeUliftFunctor (K : GrothendieckTopology 𝒟)
    (φ : P ⟶ Q) [IsLocallySurjective K φ] :
    IsLocallySurjective K (Functor.whiskerRight φ uliftFunctor.{w'}) where
  imageSieve_mem s := by
    convert imageSieve_mem K φ s.down using 1
    ext Y f
    exact ⟨fun ⟨t, ht⟩ => ⟨t.down, congrArg ULift.down ht⟩,
      fun ⟨t, ht⟩ => ⟨ULift.up t, congrArg ULift.up ht⟩⟩

/-- **Lowering the universe of the values of a presheaf preserves local surjectivity.** A section
of `Q` is the underlying section of one of `Q ⋙ uliftFunctor`, and a local lift of that is a
local lift of it.

This is the converse of `CategoryTheory.Presheaf.isLocallySurjective_whiskerRight_typeUliftFunctor`
and is stated as a plain lemma rather than an instance, the universe `w'` not being determined by
the conclusion. -/
lemma isLocallySurjective_of_whiskerRight_typeUliftFunctor (K : GrothendieckTopology 𝒟)
    (φ : P ⟶ Q)
    (hφ : IsLocallySurjective K (Functor.whiskerRight φ uliftFunctor.{w'})) :
    IsLocallySurjective K φ := by
  refine ⟨fun {V} s ↦ K.superset_covering ?_
    (imageSieve_mem K (Functor.whiskerRight φ uliftFunctor.{w'})
      (ULift.up s : (Q ⋙ uliftFunctor.{w'}).obj (op V)))⟩
  rintro W g ⟨r, hr⟩
  exact ⟨r.down, congrArg ULift.down hr⟩

/-- Raising the universe of the values of a presheaf changes nothing about local surjectivity. -/
lemma isLocallySurjective_whiskerRight_typeUliftFunctor_iff (K : GrothendieckTopology 𝒟)
    (φ : P ⟶ Q) :
    IsLocallySurjective K (Functor.whiskerRight φ uliftFunctor.{w'}) ↔
      IsLocallySurjective K φ :=
  ⟨isLocallySurjective_of_whiskerRight_typeUliftFunctor K φ,
    fun _ ↦ isLocallySurjective_whiskerRight_typeUliftFunctor K φ⟩

/-- **Raising the universe of the values of a sheaf of types gives a sheaf.** The amalgamations of
a compatible family are the amalgamations of the family of its underlying sections. -/
lemma isSheaf_whiskerRight_typeUliftFunctor (K : GrothendieckTopology 𝒟) (hT : IsSheaf K T) :
    IsSheaf K (T ⋙ uliftFunctor.{w'}) :=
  (isSheaf_iff_isSheaf_of_type K _).2
    (Presieve.isSheaf_comp_uliftFunctor K ((isSheaf_iff_isSheaf_of_type K T).1 hT))

/-- Two sections of a sheaf which agree after restriction along every member of a covering sieve
are equal. -/
theorem eq_of_restrict_eq (K : GrothendieckTopology 𝒟) (hT : IsSheaf K T) {X : 𝒟}
    {t₁ t₂ : T.obj (op X)} {S : Sieve X} (hS : S ∈ K X)
    (h : ∀ ⦃Y : 𝒟⦄ ⦃f : Y ⟶ X⦄, S.arrows f → T.map f.op t₁ = T.map f.op t₂) :
    t₁ = t₂ :=
  ((isSheaf_iff_isSheaf_of_type K T).1 hT S hS).isSeparatedFor.ext h

/-- A map into a sheaf identifies any two sections with the same image under a locally injective
map: the two sections agree along a covering sieve, hence so do their images, and a sheaf is
separated. -/
theorem app_eq_of_app_eq (K : GrothendieckTopology 𝒟) (φ : P ⟶ Q) (ψ : P ⟶ T)
    [IsLocallyInjective K φ] (hT : IsSheaf K T) {X : 𝒟} {a b : P.obj (op X)}
    (h : φ.app (op X) a = φ.app (op X) b) :
    ψ.app (op X) a = ψ.app (op X) b := by
  refine eq_of_restrict_eq K hT (equalizerSieve_mem K φ a b h) ?_
  intro Y f hf
  have hab : P.map f.op a = P.map f.op b := hf
  rw [← NatTrans.naturality_apply ψ f.op a, ← NatTrans.naturality_apply ψ f.op b, hab]

/-- **The value of a section of `Q` under the factorisation.** Let `φ : P ⟶ Q` be locally
injective and locally surjective and let `ψ : P ⟶ T` be a map into a sheaf. A section `s` of `Q`
over `X` determines a unique section of `T` over `X` whose restriction along a morphism `f` is the
`ψ`-image of any lift of `s|_f` along `φ`.

Existence is the sheaf condition applied to the family of `ψ`-images of the chosen lifts of `s`
over the sieve where `s` lifts; uniqueness is separatedness of `T` on that same sieve. -/
theorem existsUnique_section (K : GrothendieckTopology 𝒟) (φ : P ⟶ Q) (ψ : P ⟶ T)
    [IsLocallyInjective K φ] [IsLocallySurjective K φ] (hT : IsSheaf K T) {X : 𝒟}
    (s : Q.obj (op X)) :
    ∃! t : T.obj (op X), ∀ ⦃Y : 𝒟⦄ (f : Y ⟶ X) (a : P.obj (op Y)),
      φ.app (op Y) a = Q.map f.op s → T.map f.op t = ψ.app (op Y) a := by
  have hcompat : Presieve.FamilyOfElements.Compatible
      (P := T) (R := ((imageSieve φ s : Sieve X) : Presieve X))
      (fun _Y f hf => ψ.app _ (localPreimage φ s f hf)) := by
    refine (Presieve.compatible_iff_sieveCompatible _).2 ?_
    intro Y Z f g hf
    dsimp only
    rw [← NatTrans.naturality_apply ψ g.op]
    refine app_eq_of_app_eq K φ ψ hT ?_
    rw [app_localPreimage, NatTrans.naturality_apply φ g.op, app_localPreimage, op_comp,
      Functor.map_comp_apply]
  obtain ⟨t, hamalg, -⟩ :=
    ((isSheaf_iff_isSheaf_of_type K T).1 hT (imageSieve φ s) (imageSieve_mem K φ s)) _ hcompat
  -- The characterising property holds of any section restricting to the `ψ`-images of the chosen
  -- lifts, because any two lifts of one section have the same `ψ`-image.
  have key : ∀ t' : T.obj (op X), (∀ ⦃Y : 𝒟⦄ (f : Y ⟶ X) (hf : (imageSieve φ s).arrows f),
      T.map f.op t' = ψ.app _ (localPreimage φ s f hf)) →
      ∀ ⦃Y : 𝒟⦄ (f : Y ⟶ X) (a : P.obj (op Y)),
        φ.app (op Y) a = Q.map f.op s → T.map f.op t' = ψ.app (op Y) a := by
    intro t' ht' Y f a ha
    have hf : (imageSieve φ s).arrows f := ⟨a, ha⟩
    rw [ht' f hf]
    refine app_eq_of_app_eq K φ ψ hT ?_
    rw [app_localPreimage, ha]
  refine ⟨t, key t fun {_Y} f hf => hamalg f hf, ?_⟩
  intro t' ht'
  refine eq_of_restrict_eq K hT (imageSieve_mem K φ s) ?_
  intro Y f hf
  rw [ht' f (localPreimage φ s f hf) (app_localPreimage φ s f hf), hamalg f hf]

/-- **The factorisation of a map into a sheaf through a locally bijective map.** Let `(𝒟, K)` be a
site, let `φ : P ⟶ Q` be a map of presheaves of types which is locally injective and locally
surjective — that is, which exhibits `Q` as the sheafification of `P` — and let `T` be a sheaf.
Then every map `ψ : P ⟶ T` factors through `φ` by a unique map `Q ⟶ T`.

Neither `P` nor `Q` is assumed to be a sheaf, and no sheafification functor is used, so the
statement is free of the universe hypothesis that Mathlib's
`CategoryTheory.GrothendieckTopology.W.homEquiv` needs for type-valued presheaves. -/
@[ega "0 3.5.6" "Set-valued presheaves"]
theorem existsUnique_hom_of_isLocallyBijective (K : GrothendieckTopology 𝒟) (φ : P ⟶ Q)
    (ψ : P ⟶ T) [IsLocallyInjective K φ] [IsLocallySurjective K φ] (hT : IsSheaf K T) :
    ∃! χ : Q ⟶ T, φ ≫ χ = ψ := by
  -- The value of a section, and the two halves of its characterisation.
  let val : ∀ X : 𝒟ᵒᵖ, Q.obj X → T.obj X :=
    fun X s => (existsUnique_section K φ ψ hT (X := X.unop) s).choose
  have hval : ∀ (X : 𝒟ᵒᵖ) (s : Q.obj X) ⦃Y : 𝒟⦄ (f : Y ⟶ X.unop) (a : P.obj (op Y)),
      φ.app (op Y) a = Q.map f.op s → T.map f.op (val X s) = ψ.app (op Y) a :=
    fun X s => (existsUnique_section K φ ψ hT (X := X.unop) s).choose_spec.1
  have hvaluniq : ∀ (X : 𝒟ᵒᵖ) (s : Q.obj X) (t : T.obj X),
      (∀ ⦃Y : 𝒟⦄ (f : Y ⟶ X.unop) (a : P.obj (op Y)),
        φ.app (op Y) a = Q.map f.op s → T.map f.op t = ψ.app (op Y) a) → t = val X s :=
    fun X s => (existsUnique_section K φ ψ hT (X := X.unop) s).choose_spec.2
  -- Naturality, by the uniqueness half: the restriction of a value has the property that
  -- characterises the value of the restriction.
  have hnat : ∀ ⦃X Y : 𝒟ᵒᵖ⦄ (h : X ⟶ Y) (s : Q.obj X),
      T.map h (val X s) = val Y (Q.map h s) := by
    intro X Y h s
    refine hvaluniq Y (Q.map h s) _ ?_
    intro Z f a ha
    have hcomp : h ≫ f.op = (f ≫ h.unop).op := by rw [op_comp, Quiver.Hom.op_unop]
    rw [← Functor.map_comp_apply, hcomp]
    refine hval X s (f ≫ h.unop) a ?_
    rw [ha, ← hcomp, Functor.map_comp_apply]
  refine ⟨{ app := fun X => ↾fun s => val X s, naturality := ?_ }, ?_, ?_⟩
  · intro X Y h
    ext s
    simpa using (hnat h s).symm
  · ext X a
    simpa using hval X (φ.app X a) (𝟙 X.unop) a (by simp)
  · intro χ hχ
    ext X s
    refine hvaluniq X s (χ.app X s) ?_
    intro Y f a ha
    rw [← NatTrans.naturality_apply χ f.op s, ← ha, ← NatTrans.comp_app_apply, hχ]

end Presheaf

namespace Functor

universe vb v u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{vb} 𝒞] {𝒮 : Type u₂} [Category.{v} 𝒮]
  {𝒮' : Type u₃} [Category.{v} 𝒮'] {𝒳 : Type u₄} [Category.{v} 𝒳]

/-- **The morphism half of the universal property of stackification, Stacks 0435.** Let `(𝒞, J)`
be a site, let `p : 𝒮 ⥤ 𝒞`, `p' : 𝒮' ⥤ 𝒞` and `q : 𝒳 ⥤ 𝒞` be fibred categories over `𝒞` and let
`G : 𝒮 ⥤ 𝒮'` and `F : 𝒮 ⥤ 𝒳` be 1-morphisms of fibred categories over `𝒞`. Fix `U` and objects
`x`, `y` of the fibre of `𝒮` over `U`, and assume

* the map `Mor(x, y) ⟶ Mor(G x, G y)` of presheaves on `𝒞/U` induced by `G` is locally injective
  and locally surjective, i.e. exhibits its target as the sheafification of its source — clause
  (1) of Stacks 02ZN for `G` at `x` and `y`; and
* the presheaf `Mor(F x, F y)` on `𝒞/U` is a sheaf, which it is when `q` is a stack — clause (2)
  of Stacks 026F for `q` at `F x` and `F y`.

Then there is a unique map `Mor(G x, G y) ⟶ Mor(F x, F y)` of presheaves on `𝒞/U` through which
the map induced by `F` factors. Any 1-morphism `H : 𝒮' ⥤ 𝒳` over `𝒞` with `F ≅ G ⋙ H` induces
that map, so this pins the action of the extension of `F` along `G` on morphisms between objects
in the image of `G`. -/
theorem existsUnique_morPresheafMap_fac {J : GrothendieckTopology 𝒞} {p : 𝒮 ⥤ 𝒞} {p' : 𝒮' ⥤ 𝒞}
    {q : 𝒳 ⥤ 𝒞} {G : 𝒮 ⥤ 𝒮'} {F : 𝒮 ⥤ 𝒳} [p.IsFibered] [p'.IsFibered] [q.IsFibered]
    (hG : p.IsFibredOneMorphism p' G) (hF : p.IsFibredOneMorphism q F) {U : 𝒞} (x y : p.Fiber U)
    (hinj : Presheaf.IsLocallyInjective (J.over U) (hG.morPresheafMap x y))
    (hsurj : Presheaf.IsLocallySurjective (J.over U) (hG.morPresheafMap x y))
    (hq : IsMorSheaf q J U ((fiberFunctorOfCompEq hF.comp_eq U).obj x)
      ((fiberFunctorOfCompEq hF.comp_eq U).obj y)) :
    ∃! χ : morPresheaf p' ((fiberFunctorOfCompEq hG.comp_eq U).obj x)
          ((fiberFunctorOfCompEq hG.comp_eq U).obj y) ⟶
        morPresheaf q ((fiberFunctorOfCompEq hF.comp_eq U).obj x)
          ((fiberFunctorOfCompEq hF.comp_eq U).obj y),
      hG.morPresheafMap x y ≫ χ = hF.morPresheafMap x y :=
  Presheaf.existsUnique_hom_of_isLocallyBijective (J.over U) (hG.morPresheafMap x y)
    (hF.morPresheafMap x y) hq

/-- **The morphism half of Stacks 0435, in the form its hypotheses are given in.** Let `(𝒞, J)` be
a site, let `p : 𝒮 ⥤ 𝒞` be a fibred category, let `G : 𝒮 ⥤ 𝒮'` be a 1-morphism of fibred
categories over `𝒞` whose target is a stack and which satisfies clause (1) of Stacks 02ZN — so
that `G` exhibits `𝒮'` as the stackification of `𝒮` as far as morphisms are concerned — and let
`F : 𝒮 ⥤ 𝒳` be a 1-morphism of fibred categories over `𝒞` into a stack. Then for every `U` and
all `x`, `y` in the fibre of `𝒮` over `U` the map of presheaves on `𝒞/U` induced by `F` factors
uniquely through the one induced by `G`.

This is `CategoryTheory.Functor.existsUnique_morPresheafMap_fac` with the two conditions supplied
from the hypotheses that provide them: the sheaf condition on `Mor(F x, F y)` is clause (2) of
Stacks 026F for the stack `q`, and the local bijectivity is clause (1) of Stacks 02ZN for `G`. -/
theorem existsUnique_morPresheafMap_fac_of_isStack {J : GrothendieckTopology 𝒞} {p : 𝒮 ⥤ 𝒞}
    {p' : 𝒮' ⥤ 𝒞} {q : 𝒳 ⥤ 𝒞} {G : 𝒮 ⥤ 𝒮'} {F : 𝒮 ⥤ 𝒳} [p.IsFibered] (hp' : p'.IsStack J)
    (hq : q.IsStack J) (hG : p.IsFibredOneMorphism p' G) (hF : p.IsFibredOneMorphism q F)
    (hmor : haveI : p'.IsFibered := hp'.isFibered
      ∀ (U : 𝒞) (x y : p.Fiber U),
        Presheaf.IsLocallyInjective (J.over U) (hG.morPresheafMap x y) ∧
          Presheaf.IsLocallySurjective (J.over U) (hG.morPresheafMap x y))
    (U : 𝒞) (x y : p.Fiber U) :
    haveI : p'.IsFibered := hp'.isFibered
    haveI : q.IsFibered := hq.isFibered
    ∃! χ : morPresheaf p' ((fiberFunctorOfCompEq hG.comp_eq U).obj x)
          ((fiberFunctorOfCompEq hG.comp_eq U).obj y) ⟶
        morPresheaf q ((fiberFunctorOfCompEq hF.comp_eq U).obj x)
          ((fiberFunctorOfCompEq hF.comp_eq U).obj y),
      hG.morPresheafMap x y ≫ χ = hF.morPresheafMap x y := by
  have := hp'.isFibered
  have := hq.isFibered
  exact existsUnique_morPresheafMap_fac hG hF x y (hmor U x y).1 (hmor U x y).2
    (hq.isMorSheaf U _ _)

end Functor

end CategoryTheory
