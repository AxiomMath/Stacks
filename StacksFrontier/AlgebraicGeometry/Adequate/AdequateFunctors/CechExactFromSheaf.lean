module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.Descent
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.SheafCriterion

/-!
# The Čech condition of a module-valued functor, from the sheaf condition

`AdequateFunctor.isAdequate_of_descent`, the library's form of [Stacks, Tag 06VH], descends
adequacy of a module-valued functor along a ring map once the values of the functor form an
exact Čech equalizer for that map — the hypothesis `AdequateFunctor.CechExact`. This module
supplies that hypothesis *from the sheaf condition*, for a functor whose values are the sections
of a sheaf over the spectra of the algebras.

The direction matters. `PresheafOfModules.exists_restrictₛₗ_eq_of_cechDiff₀_eq_zero` and
`PresheafOfModules.isSheafFor_ofArrows_of_amitsurDiff₀` run from degree-zero exactness of an
Amitsur complex *to* the sheaf condition, and
`Stacks.Adequate.acyclic_amitsurExtendedCochainComplex_baseSections` proves that exactness for
an adequate sheaf. Here the sheaf condition is the input and the Čech equalizer is the output,
so nothing about adequacy is used or needed: `AdequateFunctor.CechExactOn` speaks only about
values of the sheaf — injectivity of one restriction map and a description of the kernel of the
next — and is therefore independent of adequacy of the kernels on the site domain.

## Main definitions

* `AdequateFunctor.CechExactOn` is the Čech condition of [Stacks, Tag 06VH] asked of a chosen
  domain of `A`-algebras, with the two Čech faces compared by an ordinary equality as in
  `AdequateFunctor.cechExact_iff_eq`. A module-valued functor coming from a sheaf of modules on
  a big site is defined only on the algebras whose spectra belong to the site, so the condition
  cannot be asked of all `A`-algebras; the two tensor products are still required to be the
  coproducts formed in all `A`-algebras, where they are computed.

## Main results

* `Stacks.CechSite.isPushout_of_isColimit_binaryCofan`: the two coproducts of [Stacks, Tag
  06VH] make the pair of Čech faces `jB, q : B₁ ⟶ B₂` a pushout of `iB : B ⟶ B₁` along itself.
  This is the algebraic step: it is what makes `Spec B₂` the fibre product of `Spec B₁` with
  itself over `Spec B`, so that the sheaf condition for the one-element covering
  `Spec B₁ → Spec B` is about exactly the two faces the Čech condition names.
* `Stacks.CechSite.injective_and_exists_eq_of_isSheafFor_singleton` brings the sheaf condition
  for a one-element covering down to elements: restriction along the covering morphism is
  injective, and a section over the cover is a restriction exactly when its two restrictions to
  the fibre product agree.
* `AdequateFunctor.cechExactOn_of_isSheafFor` combines the two:
  `AdequateFunctor.CechExactOn` holds for a functor realized as the sections of a presheaf of
  types along a "spectrum" functor, given the one-element sheaf condition for the base changes
  of `Spec A' → Spec A` and the fibre-product property of their spectra.
  `AdequateFunctor.cechExactOn_of_isSheaf` is its form for a sheaf on a site, the sheaf
  condition being replaced by covering-sieve membership.
* `AdequateFunctor.cechExact_of_cechExactOn` is the compatibility with
  `AdequateFunctor.CechExact`: on the full domain of all `A`-algebras the two conditions
  coincide, so what `AdequateFunctor.isAdequate_of_descent` consumes is a `CechExactOn` of the
  identity domain. `AdequateFunctor.isAdequate_of_descent_of_cechExactOn` is
  `AdequateFunctor.isAdequate_of_descent` with its Čech hypothesis asked in that form.

The instance at the affine-section functor of a sheaf of modules on a chosen big site is
`Stacks.Adequate.cechExactOn_affineSectionFunctor`, in
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/CechExactAffineSections.lean`.

## Implementation notes

The site is kept as a variable throughout, and the comparison between the values of the functor
and the sections of the presheaf is carried as a family of bijections with a naturality
equation rather than as an isomorphism of functors: for the affine-section functor that family
is the identity and the naturality equation is `rfl`.

`Stacks.CechSite.cofanDesc` and its three lemmas exist only to give the morphism out of a binary
coproduct a type mentioning the apex. `CategoryTheory.Limits.BinaryCofan.IsColimit.desc`
produces a morphism out of the *point of the cofan*, which is the apex only after unfolding a
semireducible definition; a goal containing such a term is not type-correct at the transparency
`rw` works at, and the rewrites below fail with an application type mismatch.

Nothing here mentions a topology, and neither geometric hypothesis of
`AdequateFunctor.cechExactOn_of_isSheafFor` is discharged at this generality; both are
discharged or recorded as owed in the big-site instance.

## References

* [Stacks Project, Tag 06VH](https://stacks.math.columbia.edu/tag/06VH)
* [Stacks Project, Tag 06VL](https://stacks.math.columbia.edu/tag/06VL)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe w v u m v₁ u₁ v₂ u₂

namespace Stacks.CechSite

/-- The morphism out of a binary coproduct determined by a pair of morphisms, with the
coproduct spelled as the apex rather than as the point of the cofan. The ascribed type is what
makes the term usable in a rewrite: the point of `CategoryTheory.Limits.BinaryCofan.mk` is the
apex only after unfolding a semireducible definition, and a goal mentioning it is not
type-correct at the transparency `rw` works at. -/
private def cofanDesc {C : Type u} [Category.{v} C] {X Y W : C} {inl : X ⟶ W} {inr : Y ⟶ W}
    (h : IsColimit (BinaryCofan.mk inl inr)) {T : C} (a : X ⟶ T) (b : Y ⟶ T) : W ⟶ T :=
  BinaryCofan.IsColimit.desc h a b

private lemma inl_cofanDesc {C : Type u} [Category.{v} C] {X Y W : C} {inl : X ⟶ W}
    {inr : Y ⟶ W} (h : IsColimit (BinaryCofan.mk inl inr)) {T : C} (a : X ⟶ T) (b : Y ⟶ T) :
    inl ≫ cofanDesc h a b = a :=
  BinaryCofan.IsColimit.inl_desc h a b

private lemma inr_cofanDesc {C : Type u} [Category.{v} C] {X Y W : C} {inl : X ⟶ W}
    {inr : Y ⟶ W} (h : IsColimit (BinaryCofan.mk inl inr)) {T : C} (a : X ⟶ T) (b : Y ⟶ T) :
    inr ≫ cofanDesc h a b = b :=
  BinaryCofan.IsColimit.inr_desc h a b

private lemma cofan_hom_ext {C : Type u} [Category.{v} C] {X Y W : C} {inl : X ⟶ W}
    {inr : Y ⟶ W} (h : IsColimit (BinaryCofan.mk inl inr)) {T : C} {a b : W ⟶ T}
    (h₁ : inl ≫ a = inl ≫ b) (h₂ : inr ≫ a = inr ≫ b) : a = b :=
  BinaryCofan.IsColimit.hom_ext h h₁ h₂

/-- Two binary coproducts give a pushout square. -/
public theorem isPushout_of_isColimit_binaryCofan {C : Type u} [Category.{v} C]
    {B A' B₁ B₂ : C} {iB : B ⟶ B₁} {iA : A' ⟶ B₁} {jB : B₁ ⟶ B₂} {jA : A' ⟶ B₂}
    {q : B₁ ⟶ B₂}
    (hc₁ : IsColimit (BinaryCofan.mk iB iA)) (hc₂ : IsColimit (BinaryCofan.mk jB jA))
    (e₁ : iB ≫ q = iB ≫ jB) (e₂ : iA ≫ q = jA) :
    IsPushout iB iB jB q where
  w := e₁.symm
  isColimit' := by
    refine ⟨PushoutCocone.IsColimit.mk _
      (fun s => cofanDesc hc₂ s.inl (iA ≫ s.inr)) (fun s => inl_cofanDesc hc₂ _ _)
      (fun s => ?_) (fun s m h₁ h₂ => ?_)⟩
    · refine cofan_hom_ext hc₁ ?_ ?_
      · rw [← Category.assoc, e₁, Category.assoc, inl_cofanDesc, s.condition]
      · rw [← Category.assoc, e₂, inr_cofanDesc]
    · refine cofan_hom_ext hc₂ ?_ ?_
      · rw [h₁, inl_cofanDesc]
      · rw [inr_cofanDesc, ← e₂, Category.assoc, h₂]

/-- **The sheaf condition for a one-element covering, at the level of elements.**

For a sheaf of types, a morphism `g` whose one-element presieve generates a covering sieve, and
a choice `p₁, p₂` of fibre product of `g` with itself: restriction along `g` is injective, and a
section over the cover is a restriction exactly when its two restrictions to the fibre product
agree.

This is the converse direction to
`PresheafOfModules.exists_restrictₛₗ_eq_of_cechDiff₀_eq_zero`, which runs from degree-zero
exactness of an Amitsur complex *to* the sheaf condition. Here the sheaf condition is the input
and the degree-zero Čech equalizer is the output. -/
public theorem injective_and_exists_eq_of_isSheafFor_singleton {C : Type u₂} [Category.{v₂} C]
    {G : Cᵒᵖ ⥤ Type w} {U₀ U₁ U₂ : C} (g : U₁ ⟶ U₀) (p₁ p₂ : U₂ ⟶ U₁)
    (hsf : Presieve.IsSheafFor G (Presieve.singleton g)) (hpb : IsPullback p₁ p₂ g g) :
    Function.Injective (G.map g.op) ∧
      ∀ y : G.obj (op U₁),
        (G.map p₁.op y = G.map p₂.op y ↔ ∃ x : G.obj (op U₀), G.map g.op x = y) := by
  have hbij := (AlgebraicGeometry.isSheafFor_singleton_iff_bijective_mapToEqualizer
    g p₁ p₂ hpb).1 hsf
  refine ⟨fun a b hab => hbij.1 (Subtype.ext hab), fun y => ⟨fun hy => ?_, fun hy => ?_⟩⟩
  · obtain ⟨x, hx⟩ := hbij.2 ⟨y, hy⟩
    exact ⟨x, congrArg Subtype.val hx⟩
  · obtain ⟨x, hx⟩ := hy
    rw [← hx, ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
      ← op_comp, ← op_comp, hpb.w]

/-- `Stacks.CechSite.injective_and_exists_eq_of_isSheafFor_singleton` for a sheaf on a site and
a morphism whose one-element presieve generates a covering sieve. -/
public theorem injective_and_exists_eq_of_isSheaf {C : Type u₂} [Category.{v₂} C]
    (J : GrothendieckTopology C) (G : Cᵒᵖ ⥤ Type w) (hG : Presieve.IsSheaf J G)
    {U₀ U₁ U₂ : C} (g : U₁ ⟶ U₀) (p₁ p₂ : U₂ ⟶ U₁)
    (hcov : Sieve.generate (Presieve.singleton g) ∈ J U₀)
    (hpb : IsPullback p₁ p₂ g g) :
    Function.Injective (G.map g.op) ∧
      ∀ y : G.obj (op U₁),
        (G.map p₁.op y = G.map p₂.op y ↔ ∃ x : G.obj (op U₀), G.map g.op x = y) :=
  injective_and_exists_eq_of_isSheafFor_singleton g p₁ p₂
    ((Presieve.isSheafFor_iff_generate _).2 (hG _ hcov)) hpb

end Stacks.CechSite

namespace AdequateFunctor

/-- The Čech condition of [Stacks, Tag 06VH] on a chosen domain of algebras.

`AdequateFunctor.CechExact` asks the condition of every triple of commutative `A`-algebras; a
module-valued functor coming from a sheaf of modules on a big site is defined only on the
algebras whose spectra belong to the site, so the condition is asked of the objects of that
domain and the two coproducts are required in all `A`-algebras, where they are computed. The
two Čech faces are compared by an ordinary equality, as in
`AdequateFunctor.cechExact_iff_eq`. -/
public abbrev CechExactOn {A : Type u} [CommRing A] {D : Type u₁} [Category.{v₁} D]
    (ι : D ⥤ CommAlgCat.{max u v} A) (F : ModuleValuedFunctorOn.{w} ι) (A' : D) : Prop :=
  ∀ (B B₁ B₂ : D) (iB : B ⟶ B₁) (iA : A' ⟶ B₁)
    (jB : B₁ ⟶ B₂) (jA : A' ⟶ B₂) (q : B₁ ⟶ B₂),
    IsColimit (BinaryCofan.mk (ι.map iB) (ι.map iA)) →
    IsColimit (BinaryCofan.mk (ι.map jB) (ι.map jA)) →
    iB ≫ q = iB ≫ jB → iA ≫ q = jA →
    (Function.Injective (F.map iB.op.op) ∧
      ∀ y : F.obj (op (op B₁)),
        (F.map jB.op.op y = F.map q.op.op y ↔
          ∃ x : F.obj (op (op B)), F.map iB.op.op x = y))

/-- On the full domain of all `A`-algebras, `AdequateFunctor.CechExactOn` is the Čech condition
of [Stacks, Tag 06VH] that `AdequateFunctor.isAdequate_of_descent` consumes. -/
public theorem cechExact_of_cechExactOn {A A' : Type u} [CommRing A] [CommRing A']
    (f : A →+* A') (F : ModuleValuedFunctor.{w, u} A)
    (h : CechExactOn (𝟭 (CommAlgCat.{u} A)) F (baseAlgebra f)) :
    CechExact f F :=
  (cechExact_iff_eq f F).2 fun B B₁ B₂ iB iA jB jA q hc₁ hc₂ e₁ e₂ =>
    h B B₁ B₂ iB iA jB jA q hc₁ hc₂ e₁ e₂

/-- [Stacks, Tag 06VH] with its Čech hypothesis in the form
`AdequateFunctor.CechExactOn`, which is the form the sheaf condition delivers. -/
public theorem isAdequate_of_descent_of_cechExactOn {A A' : Type u} [CommRing A] [CommRing A']
    (f : A →+* A') (F : ModuleValuedFunctor.{w, u} A) (F' : ModuleValuedFunctor.{w, u} A')
    (hF' : IsAdequate (𝟭 _) F')
    (hrestrict : Nonempty
      (F' ≅ (PresheafOfModules.pushforward₀ (restrictScalars f).op
        (algebraRingDiagram A)).obj F))
    (hexact : CechExactOn (𝟭 (CommAlgCat.{u} A)) F (baseAlgebra f)) :
    IsAdequate (𝟭 _) F :=
  isAdequate_of_descent f F F' hF' hrestrict (cechExact_of_cechExactOn f F hexact)

/-- **The Čech condition of [Stacks, Tag 06VH] from the sheaf condition.**

Let `F` be a module-valued functor on a domain `ι` of `A`-algebras, realized through a
"spectrum" functor `Sp` and a presheaf of types `G` on a category: the values of `F` are the
sections of `G` over the spectra, naturally (`ε`, `hε`). Then the Čech condition for a
distinguished algebra `A'` holds as soon as

* `hsf`: `G` satisfies the sheaf condition for the one-element presieve of `Sp iB`, whenever
  `ι B₁` is the coproduct of `ι B` and `ι A'` — that is, for every base change of
  `Spec A' → Spec A`; and
* `hpb`: `Sp` turns a pushout square of the algebras into a fibre-product square.

Those two are the whole input, and no topology is mentioned. The algebraic step — that the Čech
data `jB, q : B₁ ⟶ B₂` of [Stacks, Tag 06VH] *is* a pushout of `iB` along itself, so that
`Spec B₂` is the fibre product of `Spec B₁` with itself over `Spec B` — is
`Stacks.CechSite.isPushout_of_isColimit_binaryCofan`, and the passage from the sheaf condition
to the equalizer statement about elements is
`Stacks.CechSite.injective_and_exists_eq_of_isSheafFor_singleton`. -/
public theorem cechExactOn_of_isSheafFor {A : Type u} [CommRing A] {D : Type u₁}
    [Category.{v₁} D]
    (ι : D ⥤ CommAlgCat.{max u v} A) (F : ModuleValuedFunctorOn.{w} ι) (A' : D)
    {C : Type u₂} [Category.{v₂} C] (Sp : Dᵒᵖ ⥤ C) (G : Cᵒᵖ ⥤ Type w)
    (ε : ∀ X : D, F.obj (op (op X)) ≃ G.obj (op (Sp.obj (op X))))
    (hε : ∀ {X Y : D} (u : X ⟶ Y) (x : F.obj (op (op X))),
      ε Y (F.map u.op.op x) = G.map (Sp.map u.op).op (ε X x))
    (hsf : ∀ {B B₁ : D} (iB : B ⟶ B₁) (iA : A' ⟶ B₁),
      IsColimit (BinaryCofan.mk (ι.map iB) (ι.map iA)) →
      Presieve.IsSheafFor G (Presieve.singleton (Sp.map iB.op)))
    (hpb : ∀ {B B₁ B₂ : D} (iB : B ⟶ B₁) (jB q : B₁ ⟶ B₂),
      IsPushout (ι.map iB) (ι.map iB) (ι.map jB) (ι.map q) →
      IsPullback (Sp.map jB.op) (Sp.map q.op) (Sp.map iB.op) (Sp.map iB.op)) :
    CechExactOn ι F A' := by
  intro B B₁ B₂ iB iA jB jA q hc₁ hc₂ e₁ e₂
  have hpush : IsPushout (ι.map iB) (ι.map iB) (ι.map jB) (ι.map q) :=
    Stacks.CechSite.isPushout_of_isColimit_binaryCofan hc₁ hc₂
      (by rw [← ι.map_comp, ← ι.map_comp, e₁]) (by rw [← ι.map_comp, e₂])
  obtain ⟨hinj, hker⟩ := Stacks.CechSite.injective_and_exists_eq_of_isSheafFor_singleton
    (Sp.map iB.op) (Sp.map jB.op) (Sp.map q.op) (hsf iB iA hc₁) (hpb iB jB q hpush)
  refine ⟨fun a b hab => (ε B).injective (hinj ?_), fun y => ?_⟩
  · rw [← hε, ← hε, hab]
  · refine ⟨fun hy => ?_, fun hy => (ε B₂).injective ?_⟩
    · obtain ⟨x, hx⟩ := (hker (ε B₁ y)).1 (by rw [← hε, ← hε, hy])
      exact ⟨(ε B).symm x, (ε B₁).injective (by rw [hε, Equiv.apply_symm_apply, hx])⟩
    · obtain ⟨x, hx⟩ := hy
      rw [hε, hε]
      exact (hker (ε B₁ y)).2 ⟨ε B x, by rw [← hε, hx]⟩

/-- `AdequateFunctor.cechExactOn_of_isSheafFor` for a sheaf on a site, the covering hypothesis
being that the one-element presieve of each base change of `Spec A' → Spec B` generates a
covering sieve. -/
public theorem cechExactOn_of_isSheaf {A : Type u} [CommRing A] {D : Type u₁} [Category.{v₁} D]
    (ι : D ⥤ CommAlgCat.{max u v} A) (F : ModuleValuedFunctorOn.{w} ι) (A' : D)
    {C : Type u₂} [Category.{v₂} C] (J : GrothendieckTopology C) (Sp : Dᵒᵖ ⥤ C)
    (G : Cᵒᵖ ⥤ Type w) (hG : Presieve.IsSheaf J G)
    (ε : ∀ X : D, F.obj (op (op X)) ≃ G.obj (op (Sp.obj (op X))))
    (hε : ∀ {X Y : D} (u : X ⟶ Y) (x : F.obj (op (op X))),
      ε Y (F.map u.op.op x) = G.map (Sp.map u.op).op (ε X x))
    (hcov : ∀ {B B₁ : D} (iB : B ⟶ B₁) (iA : A' ⟶ B₁),
      IsColimit (BinaryCofan.mk (ι.map iB) (ι.map iA)) →
      Sieve.generate (Presieve.singleton (Sp.map iB.op)) ∈ J (Sp.obj (op B)))
    (hpb : ∀ {B B₁ B₂ : D} (iB : B ⟶ B₁) (jB q : B₁ ⟶ B₂),
      IsPushout (ι.map iB) (ι.map iB) (ι.map jB) (ι.map q) →
      IsPullback (Sp.map jB.op) (Sp.map q.op) (Sp.map iB.op) (Sp.map iB.op)) :
    CechExactOn ι F A' :=
  cechExactOn_of_isSheafFor ι F A' Sp G ε hε
    (fun iB iA hc => (Presieve.isSheafFor_iff_generate _).2 (hG _ (hcov iB iA hc))) hpb

end AdequateFunctor

end
