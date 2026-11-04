module

public import StacksFrontier.CategoryTheory.Sites.Localization.LowerShriekCoproducts
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sheaves on a localized site as sheaves over the sheafified representable

Let `(C, J)` be a site and let `U` be an object of `C`. Stacks 00Y1 asserts that `j_{U!}` induces
an equivalence `Sh(C/U) ≌ Sh(C)/h_U^#`. This file proves that, following the source's proof: the
*presheaf* level statement `PSh(C/U) ≌ PSh(C)/h_U` is proved first, and then both of the source's
identifications `j_{U!}^{PSh}F_φ = F` and `(j_{U!}^{PSh}G)_γ = G` are proved at the sheaf level,
the first giving essential surjectivity of `j_{U!}` into the slice and the second giving full
faithfulness.

Throughout, `j_U` is Mathlib's `CategoryTheory.Over.forget U` and `j_{U!}` is its
`Functor.sheafPullback`; the coproduct presheaf `V ↦ ∐_{φ : V ⟶ U} G(V →φ U)` and the presheaf
level
`j_{U!}` are `CategoryTheory.OverShriek.presheaf` and `CategoryTheory.OverShriek.presheafFunctor`
from `StacksFrontier.CategoryTheory.Sites.Localization.LowerShriekCoproducts`.

## The two constructions of the source

For a presheaf `F` on `C` and a map `φ : F ⟶ A`, together with a "tautological section"
`ρ : h_U ⟶ A`, the presheaf `fiber ρ φ` on `C/U` sends `(X, a)` to the set of `s ∈ F(X)` with
`φ(s) = ρ(a)`. Taking `A = h_U` and `ρ = 𝟙` gives the source's presheaf level functor
`PSh(C)/h_U ⟶ PSh(C/U)`, `(F, φ) ↦ F_φ`; taking `A = h_U^#` and `ρ` the sheafification map gives
its sheaf level functor `Sh(C)/h_U^# ⟶ Sh(C/U)`. One definition therefore serves both, and
`isSheaf_fiber` — the source's "it is easy to see that `(X, a) ↦ F_φ(X, a)` is a sheaf on `C/U`" —
is proved once, from the sheaf condition for `j_U^{-1}F` and separatedness of `j_U^{-1}A`.

In the other direction `G ↦ (j_{U!}G, γ)` is `presheafFunctorToOver` at the presheaf level and
`sheafFunctorToOver` at the sheaf level; that the underlying sheaf of `sheafFunctorToOver.obj G`
really is `j_{U!}G` is `sheafFunctorToOverForgetIso`, which is Stacks 03CD. Reading that
identification backwards gives the source's own restatement of Stacks 00Y1, that `j_{U!}` *is* the
equivalence `Sh(C/U) ≌ Sh(C)/h_U^#` followed by `Over.forget`; since `j_{U!}` is pinned only by its
universal property, `sheafFunctorToOverForgetIsoOfAdjunction` states it for an arbitrary left
adjoint of `j_U^{-1}`, which is the form the consequences of 00Y1 use.

## Main results

* `CategoryTheory.OverShriek.fiber`: the presheaf `(X, a) ↦ {s ∈ F(X) | φ(s) = ρ(a)}` on `C/U`.
* `CategoryTheory.OverShriek.isSheaf_fiber`: `fiber ρ φ` is a sheaf as soon as `j_U^{-1}F` is a
  sheaf and `j_U^{-1}A` is separated.
* `CategoryTheory.OverShriek.presheafEquivalence`: **the presheaf level form of Stacks 00Y1**,
  `PSh(C/U) ≌ PSh(C)/h_U`, with `presheafEquivalence_functor_comp_forget` identifying its
  underlying functor with the presheaf level `j_{U!}`.
* `CategoryTheory.OverShriek.sheafFunctorToOver` and
  `CategoryTheory.OverShriek.sheafFiberFunctor`: the two functors of the sheaf level statement.
* `CategoryTheory.OverShriek.sheafFunctorToOverForgetIso`: the underlying sheaf of
  `sheafFunctorToOver.obj G` is `j_{U!}G`, and
  `CategoryTheory.OverShriek.sheafFunctorToOverForgetIsoOfAdjunction`: the same statement for an
  arbitrary left adjoint of `j_U^{-1}` in place of the one built from `Over.forget U`.
* `CategoryTheory.OverShriek.sheafFunctorToOverObjIso`: `j_{U!}` of the fibre sheaf of
  `(F, φ)` is `(F, φ)` again, whence `sheafFunctorToOver` is essentially surjective. This is the
  source's `j_{U!}^{PSh}F_φ = F`, and it is one of the two halves of Stacks 00Y1.
* `CategoryTheory.OverShriek.sheafUnitIso`: the other half, the source's `(j_{U!}^{PSh}G)_γ = G` at
  the sheaf level, whence `sheafFunctorToOver` is fully faithful.
* `CategoryTheory.OverShriek.isEquivalence_sheafFunctorToOver` and
  `CategoryTheory.OverShriek.sheafEquivalence`: **Stacks 00Y1**, `Sh(C/U) ≌ Sh(C)/h_U^#`.

Tags covered: 00Y1.
-/

@[expose] public section

open CategoryTheory Opposite

universe v u

namespace CategoryTheory.OverShriek

variable {C : Type u} [Category.{v} C] {U : C} {A : Cᵒᵖ ⥤ Type v}

/-! ### The fibre of a map of presheaves over a tautological section -/

/-- The presheaf on `C/U` cut out of `j_U^{-1}F` by a map `φ : F ⟶ A` and a section
`ρ : h_U ⟶ A`: its sections over `(X, a)` are the `s ∈ F(X)` with `φ(s) = ρ(a)`.

For `A = h_U` and `ρ = 𝟙` this is the presheaf `F_φ` of Stacks 00Y1; for `A = h_U^#` and
`ρ = toSheafify` it is the sheaf `F_φ` of the same lemma. -/
def fiber (ρ : yoneda.obj U ⟶ A) {F : Cᵒᵖ ⥤ Type v} (φ : F ⟶ A) : (Over U)ᵒᵖ ⥤ Type v where
  obj W := {s : F.obj (op W.unop.left) //
    φ.app (op W.unop.left) s = ρ.app (op W.unop.left) W.unop.hom}
  map {W W'} g := ↾fun s => ⟨F.map g.unop.left.op s.1, by
    rw [NatTrans.naturality_apply φ g.unop.left.op s.1, s.2,
      ← NatTrans.naturality_apply ρ g.unop.left.op W.unop.hom]
    exact congrArg _ (Over.w g.unop)⟩
  map_id _ := by ext s; simp
  map_comp f g := by
    ext s
    simp only [unop_comp, Over.comp_left, op_comp, F.map_comp_apply]
    rfl

/-- The inclusion of `fiber ρ φ` into the restriction `j_U^{-1}F` of `F` to `C/U`. -/
def fiberι (ρ : yoneda.obj U ⟶ A) {F : Cᵒᵖ ⥤ Type v} (φ : F ⟶ A) :
    fiber ρ φ ⟶ (Over.forget U).op ⋙ F where
  app := fun _ => ↾fun s => s.1
  naturality _ _ _ := rfl

/-- A morphism `(F, φ) ⟶ (F', φ')` of presheaves over `A` induces a map of fibres. -/
def fiberMap (ρ : yoneda.obj U ⟶ A) {T T' : Over A} (f : T ⟶ T') :
    fiber ρ T.hom ⟶ fiber ρ T'.hom where
  app W := ↾fun s => ⟨f.left.app (op W.unop.left) s.1, by
    rw [← NatTrans.comp_app_apply, Over.w f, s.2]⟩
  naturality {W W'} g := by
    ext s
    refine Subtype.ext ?_
    exact NatTrans.naturality_apply f.left g.unop.left.op s.1

/-- The fibre construction as a functor `PSh(C)/A ⥤ PSh(C/U)`. -/
@[sga "3 I 1.4" "more general"]
def fiberFunctor (ρ : yoneda.obj U ⟶ A) : Over A ⥤ ((Over U)ᵒᵖ ⥤ Type v) where
  obj T := fiber ρ T.hom
  map f := fiberMap ρ f
  map_id _ := by ext W s; rfl
  map_comp f g := by ext W s; rfl

/-- **The fibre presheaf is a sheaf.** If the restriction `j_U^{-1}F` of `F` to `C/U` is a sheaf
and the restriction `j_U^{-1}A` of `A` is separated, then `fiber ρ φ` is a sheaf on `C/U`.

Indeed a compatible family of sections of `fiber ρ φ` amalgamates uniquely in `j_U^{-1}F`, and the
resulting section `t` satisfies `φ(t) = ρ(W.hom)` because both sides of that equation have the same
restriction along every arrow of the covering sieve. -/
lemma isSheaf_fiber {K : GrothendieckTopology (Over U)} (ρ : yoneda.obj U ⟶ A)
    {F : Cᵒᵖ ⥤ Type v} (φ : F ⟶ A)
    (hF : Presieve.IsSheaf K ((Over.forget U).op ⋙ F))
    (hA : Presieve.IsSeparated K ((Over.forget U).op ⋙ A)) :
    Presieve.IsSheaf K (fiber ρ φ) := by
  intro W S hS x hx
  obtain ⟨t, ht, htu⟩ := hF S hS (x.map (fiberι ρ φ)) (hx.map _)
  have hmem : φ.app (op W.left) t = ρ.app (op W.left) W.hom := by
    refine (hA S hS).ext (fun {Y} {f} hf => ?_)
    simp only [Functor.comp_map, Functor.op_map, Over.forget_map, Quiver.Hom.unop_op]
    rw [← NatTrans.naturality_apply φ f.left.op t, ← NatTrans.naturality_apply ρ f.left.op W.hom]
    simp only [yoneda_obj_map, TypeCat.ofHom_apply, Quiver.Hom.unop_op]
    rw [Over.w f, show F.map f.left.op t = (x f hf).1 from ht f hf]
    exact (x f hf).2
  refine ⟨⟨t, hmem⟩, fun {Y} f hf => Subtype.ext (ht f hf), fun y hy => Subtype.ext ?_⟩
  exact htu y.1 (fun {Y} f hf => congrArg Subtype.val (hy f hf))

/-! ### The presheaf level statement -/

/-- The structural map `∐_{φ : V ⟶ U} G(V →φ U) ⟶ h_U` of the coproduct presheaf, forgetting the
section and keeping the morphism to `U`. This is the map `γ` of Stacks 00Y1. -/
def presheafToYoneda (G : (Over U)ᵒᵖ ⥤ Type v) : presheaf G ⟶ yoneda.obj U where
  app := fun _ => ↾fun p => p.1
  naturality _ _ _ := rfl

/-- The presheaf level `j_{U!}`, viewed as a functor `PSh(C/U) ⥤ PSh(C)/h_U` by means of `γ`. -/
def presheafFunctorToOver : ((Over U)ᵒᵖ ⥤ Type v) ⥤ Over (yoneda.obj U) :=
  (presheafFunctor (U := U)).toOver (yoneda.obj U) presheafToYoneda
    (fun {_ _} _ => by ext _ _; rfl)

/-- The sections of `G` over `(X, a)` are the sections `(ψ, s)` of the coproduct presheaf over `X`
with `ψ = a`: this is the source's `(j_{U!}^{PSh}G)_γ = G`. -/
def presheafUnitEquiv (G : (Over U)ᵒᵖ ⥤ Type v) (W : (Over U)ᵒᵖ) :
    G.obj W ≃ (fiber (𝟙 (yoneda.obj U)) (presheafToYoneda G)).obj W :=
  (Equiv.sigmaSubtype (β := fun ψ : W.unop.left ⟶ U => G.obj (op (Over.mk ψ))) W.unop.hom).symm

/-- A presheaf `F` over `h_U` is the disjoint union of the fibres of its structural map: this is
the source's `j_{U!}^{PSh}F_φ = F`. -/
def presheafCounitEquiv (T : Over (yoneda.obj U)) (V : Cᵒᵖ) :
    (presheaf (fiber (𝟙 (yoneda.obj U)) T.hom)).obj V ≃ T.left.obj V :=
  Equiv.sigmaFiberEquiv (fun s => T.hom.app V s)

/-- `presheafUnitEquiv`, as an isomorphism of presheaves on `C/U`. -/
def presheafUnitIsoApp (G : (Over U)ᵒᵖ ⥤ Type v) :
    G ≅ fiber (𝟙 (yoneda.obj U)) (presheafToYoneda G) :=
  NatIso.ofComponents (fun W => (presheafUnitEquiv G W).toIso) (fun {W W'} g => by
    ext s
    refine Subtype.ext ?_
    exact (sigmaMk_eq G s (Over.homMk g.unop.left rfl :
      Over.mk (g.unop.left ≫ W.unop.hom) ⟶ Over.mk W.unop.hom) g.unop rfl).symm)

/-- The unit isomorphism of `presheafEquivalence`. -/
def presheafUnitIso :
    𝟭 ((Over U)ᵒᵖ ⥤ Type v) ≅ presheafFunctorToOver ⋙ fiberFunctor (𝟙 (yoneda.obj U)) :=
  NatIso.ofComponents presheafUnitIsoApp (fun _ => by ext W s; refine Subtype.ext ?_; rfl)

/-- The counit isomorphism of `presheafEquivalence`. -/
def presheafCounitIso :
    fiberFunctor (𝟙 (yoneda.obj U)) ⋙ presheafFunctorToOver ≅ 𝟭 (Over (yoneda.obj U)) :=
  NatIso.ofComponents
    (fun T => Over.isoMk (NatIso.ofComponents (fun V => (presheafCounitEquiv T V).toIso)
        (fun _ => by ext p; rfl)) (by ext V p; exact p.2.property))
    (fun _ => by ext V p; rfl)

/-- **The presheaf level form of Stacks 00Y1.** The presheaf level `j_{U!}` is an equivalence
`PSh(C/U) ≌ PSh(C)/h_U`, with inverse `(F, φ) ↦ F_φ`. -/
def presheafEquivalence : ((Over U)ᵒᵖ ⥤ Type v) ≌ Over (yoneda.obj U) where
  functor := presheafFunctorToOver
  inverse := fiberFunctor (𝟙 (yoneda.obj U))
  unitIso := presheafUnitIso
  counitIso := presheafCounitIso
  functor_unitIso_comp _ := by ext V p; rfl

/-- The functor of `presheafEquivalence` really is the presheaf level `j_{U!}` of Stacks 03CD. -/
lemma presheafEquivalence_functor_comp_forget :
    (presheafEquivalence (U := U)).functor ⋙ Over.forget (yoneda.obj U) = presheafFunctor :=
  rfl

/-! ### The comparison map `j_{U!}^{PSh}F_φ ⟶ F` -/

/-- The canonical map `∐_a F_φ(-, a) ⟶ F`, forgetting `a` and keeping the section of `F`. When
`ρ = 𝟙` it is an isomorphism (`presheafCounitEquiv`); in general it is only locally bijective. -/
def fiberCoproductToBase (ρ : yoneda.obj U ⟶ A) {F : Cᵒᵖ ⥤ Type v} (φ : F ⟶ A) :
    presheaf (fiber ρ φ) ⟶ F where
  app := fun _ => ↾fun p => p.2.val
  naturality _ _ _ := rfl

/-- The cartesian square defining the fibre: the section of `F` and the morphism to `U` carried by
a section of `∐_a F_φ(-, a)` have the same image in `A`. -/
lemma fiberCoproductToBase_comp (ρ : yoneda.obj U ⟶ A) {F : Cᵒᵖ ⥤ Type v} (φ : F ⟶ A) :
    fiberCoproductToBase ρ φ ≫ φ = presheafToYoneda (fiber ρ φ) ≫ ρ := by
  ext V p
  exact p.2.property

/-- Two sections of `∐_a F_φ(-, a)` over `V` agree as soon as their morphisms to `U` agree and
their underlying sections of `F` agree. -/
lemma presheaf_fiber_ext {ρ : yoneda.obj U ⟶ A} {F : Cᵒᵖ ⥤ Type v} {φ : F ⟶ A} {V : Cᵒᵖ}
    {p q : (presheaf (fiber ρ φ)).obj V} (h₁ : p.1 = q.1)
    (h₂ : (p.2.val : F.obj V) = q.2.val) : p = q :=
  Sigma.subtype_ext h₁ h₂

/-- If `ρ` is locally surjective then so is `∐_a F_φ(-, a) ⟶ F`: a section `s` of `F` over `X`
lifts over any arrow along which `φ(s)` is in the image of `ρ`. -/
instance isLocallySurjective_fiberCoproductToBase (J : GrothendieckTopology C)
    (ρ : yoneda.obj U ⟶ A) {F : Cᵒᵖ ⥤ Type v} (φ : F ⟶ A) [Presheaf.IsLocallySurjective J ρ] :
    Presheaf.IsLocallySurjective J (fiberCoproductToBase ρ φ) where
  imageSieve_mem {X} s := by
    refine J.superset_covering ?_ (Presheaf.imageSieve_mem J ρ (φ.app (op X) s))
    rintro V g ⟨a, ha⟩
    exact ⟨⟨a, F.map g.op s, (NatTrans.naturality_apply φ g.op s).trans ha.symm⟩, rfl⟩

/-- If `ρ` is locally injective then so is `∐_a F_φ(-, a) ⟶ F`: two sections with the same image in
`F` carry morphisms to `U` with the same image under `ρ`, hence locally equal. -/
instance isLocallyInjective_fiberCoproductToBase (J : GrothendieckTopology C)
    (ρ : yoneda.obj U ⟶ A) {F : Cᵒᵖ ⥤ Type v} (φ : F ⟶ A) [Presheaf.IsLocallyInjective J ρ] :
    Presheaf.IsLocallyInjective J (fiberCoproductToBase ρ φ) where
  equalizerSieve_mem {X} p q h := by
    have h' : (p.2.val : F.obj X) = q.2.val := h
    have hpq : ρ.app X p.1 = ρ.app X q.1 :=
      (p.2.property.symm.trans (congrArg (φ.app X) h')).trans q.2.property
    refine J.superset_covering ?_ (Presheaf.equalizerSieve_mem J ρ p.1 q.1 hpq)
    intro V g hg
    exact presheaf_fiber_ext hg (congrArg (F.map g.op) h')

/-! ### The sheaf level statement -/

noncomputable section

variable (J : GrothendieckTopology C) [HasWeakSheafify J (Type v)]

/-- If a map into a sheaf `F` and a map into a presheaf `Q` agree after `Q ⟶ Q^#`, then the induced
map `P^# ⟶ F ≅ (F.obj)^# ⟶ Q^#` is the sheafification of the second one. This is the bookkeeping
needed to turn a commuting square of presheaves into an isomorphism in `Sh(C)/Q^#`. -/
lemma presheafToSheaf_map_comp_counit {P Q : Cᵒᵖ ⥤ Type v} {F : Sheaf J (Type v)}
    (κ : P ⟶ F.obj) (γ : P ⟶ Q) (ψ : F ⟶ (presheafToSheaf J (Type v)).obj Q)
    (h : κ ≫ ψ.hom = γ ≫ toSheafify J Q) :
    ((presheafToSheaf J (Type v)).map κ ≫
        (sheafificationAdjunction J (Type v)).counit.app F) ≫ ψ =
      (presheafToSheaf J (Type v)).map γ := by
  refine Sheaf.hom_ext (sheafify_hom_ext J _ _
    ((presheafToSheaf J (Type v)).obj Q).property ?_)
  have e : ∀ {X Y : Cᵒᵖ ⥤ Type v} (f : X ⟶ Y),
      toSheafify J X ≫ sheafifyMap J f = f ≫ toSheafify J Y :=
    fun f => (toSheafify_naturality J f).symm
  change toSheafify J P ≫ (sheafifyMap J κ ≫
    ((sheafificationAdjunction J (Type v)).counit.app F).hom) ≫ ψ.hom =
      toSheafify J P ≫ sheafifyMap J γ
  rw [e γ, ← h, ← Category.assoc, ← Category.assoc, e κ]
  simp

/-- The sheaf level `j_{U!}`, viewed as a functor `Sh(C/U) ⥤ Sh(C)/h_U^#`: a sheaf `G` on `C/U` is
sent to the sheafification of the coproduct presheaf, over the sheafification of `γ`.

That its underlying sheaf is `j_{U!}G` is `sheafFunctorToOverForgetIso`. -/
def sheafFunctorToOver :
    Sheaf (J.over U) (Type v) ⥤ Over ((presheafToSheaf J (Type v)).obj (yoneda.obj U)) :=
  sheafToPresheaf (J.over U) (Type v) ⋙ presheafFunctorToOver ⋙
    Over.post (presheafToSheaf J (Type v))

/-- The presheaf underlying `sheafFiberFunctor.obj (F, φ)`, namely `fiber (toSheafify) φ`. -/
def sheafFiberUnderlying :
    Over ((presheafToSheaf J (Type v)).obj (yoneda.obj U)) ⥤ ((Over U)ᵒᵖ ⥤ Type v) :=
  Over.post (sheafToPresheaf J (Type v)) ⋙ fiberFunctor (toSheafify J (yoneda.obj U))

/-- `sheafFiberUnderlying` takes values in sheaves: this is `isSheaf_fiber` applied to the
restrictions of the sheaf `F` and of the sheaf `h_U^#` to `C/U`. -/
lemma isSheaf_sheafFiberUnderlying
    (T : Over ((presheafToSheaf J (Type v)).obj (yoneda.obj U))) :
    Presheaf.IsSheaf (J.over U) ((sheafFiberUnderlying (U := U) J).obj T) := by
  rw [isSheaf_iff_isSheaf_of_type]
  refine isSheaf_fiber _ _ ((isSheaf_iff_isSheaf_of_type _ _).1 (T.left.over U).property) ?_
  exact ((isSheaf_iff_isSheaf_of_type _ _).1
    (((presheafToSheaf J (Type v)).obj (yoneda.obj U)).over U).property).isSeparated

/-- The sheaf level fibre functor `Sh(C)/h_U^# ⥤ Sh(C/U)` of Stacks 00Y1: a sheaf `F` with a map
`φ : F ⟶ h_U^#` is sent to `(X, a) ↦ {s ∈ F(X) | φ(s) = a^#}`. -/
def sheafFiberFunctor :
    Over ((presheafToSheaf J (Type v)).obj (yoneda.obj U)) ⥤ Sheaf (J.over U) (Type v) :=
  ObjectProperty.lift _ (sheafFiberUnderlying J) (isSheaf_sheafFiberUnderlying J)

variable [J.WEqualsLocallyBijective (Type v)]

/-- The comparison map `∐_a F_φ(-, a) ⟶ F` is locally bijective, hence becomes an isomorphism after
sheafification, whenever the tautological section `ρ` is locally bijective. -/
lemma isIso_map_fiberCoproductToBase (ρ : yoneda.obj U ⟶ A) {F : Cᵒᵖ ⥤ Type v} (φ : F ⟶ A)
    [Presheaf.IsLocallySurjective J ρ] [Presheaf.IsLocallyInjective J ρ] :
    IsIso ((presheafToSheaf J (Type v)).map (fiberCoproductToBase ρ φ)) :=
  (J.W_iff _).1 (J.W_of_isLocallyBijective _)

/-- **One half of Stacks 00Y1**, the source's `j_{U!}^{PSh}F_φ = F` at the sheaf level: applying
`sheafFunctorToOver` to the fibre sheaf of `(F, φ)` gives back `(F, φ)`.

The comparison map `∐_a F_φ(-, a) ⟶ F` is locally bijective because `h_U ⟶ h_U^#` is, so it becomes
an isomorphism after sheafification; and the triangle over `h_U^#` commutes by
`fiberCoproductToBase_comp`. -/
def sheafFunctorToOverObjIso (T : Over ((presheafToSheaf J (Type v)).obj (yoneda.obj U))) :
    (sheafFunctorToOver (U := U) J).obj ((sheafFiberFunctor J).obj T) ≅ T := by
  have : IsIso ((presheafToSheaf J (Type v)).map (fiberCoproductToBase
      (toSheafify J (yoneda.obj U)) ((sheafToPresheaf J (Type v)).map T.hom))) :=
    isIso_map_fiberCoproductToBase J _ _
  exact Over.isoMk ((@asIso _ _ _ _ _ this) ≪≫
      asIso ((sheafificationAdjunction J (Type v)).counit.app T.left))
    (presheafToSheaf_map_comp_counit J _ _ _ (fiberCoproductToBase_comp _ _))

/-- Every sheaf over `h_U^#` is in the image of `sheafFunctorToOver`. -/
instance essSurj_sheafFunctorToOver : (sheafFunctorToOver (U := U) J).EssSurj where
  mem_essImage T := ⟨(sheafFiberFunctor J).obj T, ⟨sheafFunctorToOverObjIso J T⟩⟩

/-! ### The unit `G ⟶ (j_{U!}G)_γ`, and Stacks 00Y1

The source's remaining equality is `(j_{U!}^{PSh}G)_γ = G`, at the sheaf level. The comparison map
in that direction sends a section `s` of `G` over `(X, a)` to the section `(a, s)` of the coproduct
presheaf, viewed in its sheafification; it is `sheafUnitApp`. It is a locally bijective map of
sheaves on `C/U`, hence an isomorphism, the two local statements being obtained by transporting the
covering sieves witnessing local bijectivity of `h_U ⟶ h_U^#` and of
`∐_a G(-, a) ⟶ (∐_a G(-, a))^#` across `Sieve.overEquiv`. -/

/-- The unit of Stacks 00Y1: a section `s` of `G` over `(X, a)` is a section `(a, s)` of the
coproduct presheaf over `X`, whose image in the sheafification lies in the fibre of
`(j_{U!}G, γ)` over `a`. -/
def sheafUnitApp (G : (Over U)ᵒᵖ ⥤ Type v) :
    G ⟶ fiber (toSheafify J (yoneda.obj U)) (sheafifyMap J (presheafToYoneda G)) where
  app W := ↾fun s => ⟨(toSheafify J (presheaf G)).app (op W.unop.left) ⟨W.unop.hom, s⟩, by
    rw [← (toSheafify J (presheaf G)).comp_app_apply (sheafifyMap J (presheafToYoneda G))
        (op W.unop.left) ⟨W.unop.hom, s⟩, ← toSheafify_naturality,
      (presheafToYoneda G).comp_app_apply (toSheafify J (yoneda.obj U))
        (op W.unop.left) ⟨W.unop.hom, s⟩]
    rfl⟩
  naturality W W' g := by
    ext s
    refine Subtype.ext ?_
    have key : ((presheaf G).map ((Over.forget U).op.map g))
        (⟨W.unop.hom, s⟩ : Σ φ : W.unop.left ⟶ U, G.obj (op (Over.mk φ))) =
          ⟨W'.unop.hom, G.map g s⟩ :=
      sigmaMk_eq G s _ g.unop rfl
    exact (congrArg (fun t => (toSheafify J (presheaf G)).app (op W'.unop.left) t) key).symm.trans
      (NatTrans.naturality_apply (toSheafify J (presheaf G)) ((Over.forget U).op.map g)
        (⟨W.unop.hom, s⟩ : Σ φ : W.unop.left ⟶ U, G.obj (op (Over.mk φ))))

/-- **The unit is locally surjective.** A section `t` of the fibre of `(j_{U!}G, γ)` over
`a : X ⟶ U` comes, locally on `X`, from a section `(ψ, s)` of the coproduct presheaf: this is local
surjectivity of `∐_a G(-, a) ⟶ (∐_a G(-, a))^#`. Its morphism `ψ` need not be the given `a`, but
`ψ` and `a` have the same image in `h_U^#`, so they agree after a further refinement, by local
injectivity of `h_U ⟶ h_U^#`. Composing the two refinements with `J.transitive` and transporting
the result across `Sieve.overEquiv` gives a `J.over U`-covering sieve of `(X, a)` on which `t` is
in the image. -/
instance isLocallySurjective_sheafUnitApp (G : (Over U)ᵒᵖ ⥤ Type v) :
    Presheaf.IsLocallySurjective (J.over U) (sheafUnitApp J G) where
  imageSieve_mem {W} t := by
    rw [GrothendieckTopology.mem_over_iff]
    refine J.transitive (Presheaf.imageSieve_mem J (toSheafify J (presheaf G)) t.1) _ ?_
    intro V g hg
    obtain ⟨⟨ψ, s⟩, hp⟩ := hg
    have step1 : (sheafifyMap J (presheafToYoneda G)).app (op V)
          ((sheafify J (presheaf G)).map g.op t.1)
        = (toSheafify J (yoneda.obj U)).app (op V) (g ≫ W.hom) := by
      rw [NatTrans.naturality_apply (sheafifyMap J (presheafToYoneda G)) g.op t.1, t.2,
        ← NatTrans.naturality_apply (toSheafify J (yoneda.obj U)) g.op W.hom]
      rfl
    have key : (toSheafify J (yoneda.obj U)).app (op V) ψ
        = (toSheafify J (yoneda.obj U)).app (op V) (g ≫ W.hom) := by
      rw [← step1, ← hp, ← (toSheafify J (presheaf G)).comp_app_apply
          (sheafifyMap J (presheafToYoneda G)) (op V) ⟨ψ, s⟩, ← toSheafify_naturality,
        (presheafToYoneda G).comp_app_apply (toSheafify J (yoneda.obj U)) (op V) ⟨ψ, s⟩]
      rfl
    have hmem : Presheaf.equalizerSieve (F := yoneda.obj U) (X := op V) ψ (g ≫ W.hom) ∈ J V :=
      Presheaf.equalizerSieve_mem J _ _ _ key
    refine J.superset_covering ?_ hmem
    intro V' h hh
    rw [Sieve.pullback_apply, Sieve.overEquiv_iff]
    have hw : h ≫ ψ = (h ≫ g) ≫ W.hom := by rw [Category.assoc]; exact hh
    refine ⟨G.map (Over.homMk h hw : Over.mk ((h ≫ g) ≫ W.hom) ⟶ Over.mk ψ).op s, ?_⟩
    refine Subtype.ext ?_
    have e1 : (⟨(h ≫ g) ≫ W.hom,
          G.map (Over.homMk h hw : Over.mk ((h ≫ g) ≫ W.hom) ⟶ Over.mk ψ).op s⟩ :
            Σ φ : V' ⟶ U, G.obj (op (Over.mk φ)))
        = (presheaf G).map h.op (⟨ψ, s⟩ : Σ φ : V ⟶ U, G.obj (op (Over.mk φ))) :=
      sigmaMk_eq G s _ (Over.homMk h rfl) rfl
    calc (toSheafify J (presheaf G)).app (op V')
          (⟨(h ≫ g) ≫ W.hom,
            G.map (Over.homMk h hw : Over.mk ((h ≫ g) ≫ W.hom) ⟶ Over.mk ψ).op s⟩ :
              Σ φ : V' ⟶ U, G.obj (op (Over.mk φ)))
        = (toSheafify J (presheaf G)).app (op V')
            ((presheaf G).map h.op (⟨ψ, s⟩ : Σ φ : V ⟶ U, G.obj (op (Over.mk φ)))) :=
          congrArg (fun x => (toSheafify J (presheaf G)).app (op V') x) e1
      _ = (sheafify J (presheaf G)).map h.op
            ((toSheafify J (presheaf G)).app (op V) (⟨ψ, s⟩ :
              Σ φ : V ⟶ U, G.obj (op (Over.mk φ)))) :=
          NatTrans.naturality_apply (toSheafify J (presheaf G)) h.op _
      _ = (sheafify J (presheaf G)).map h.op ((sheafify J (presheaf G)).map g.op t.1) :=
          congrArg (fun x => (sheafify J (presheaf G)).map h.op x) hp
      _ = (sheafify J (presheaf G)).map (h ≫ g).op t.1 := by
          rw [← (sheafify J (presheaf G)).map_comp_apply, ← op_comp]

/-- **The unit is locally injective.** Two sections of `G` over `(X, a)` with the same image are
two sections `(a, x)` and `(a, y)` of the coproduct presheaf with the same image in the
sheafification, hence agree on a covering sieve of `X`; the corresponding sieve of `(X, a)` covers
for `J.over U`. -/
instance isLocallyInjective_sheafUnitApp (G : (Over U)ᵒᵖ ⥤ Type v) :
    Presheaf.IsLocallyInjective (J.over U) (sheafUnitApp J G) where
  equalizerSieve_mem {W} x y h := by
    rw [GrothendieckTopology.mem_over_iff]
    have h' : (toSheafify J (presheaf G)).app (op W.unop.left)
          (⟨W.unop.hom, x⟩ : Σ φ : W.unop.left ⟶ U, G.obj (op (Over.mk φ)))
        = (toSheafify J (presheaf G)).app (op W.unop.left)
          (⟨W.unop.hom, y⟩ : Σ φ : W.unop.left ⟶ U, G.obj (op (Over.mk φ))) :=
      congrArg Subtype.val h
    have hmem : Presheaf.equalizerSieve (F := presheaf G) (X := op W.unop.left)
        ⟨W.unop.hom, x⟩ ⟨W.unop.hom, y⟩ ∈ J W.unop.left :=
      Presheaf.equalizerSieve_mem J _ _ _ h'
    refine J.superset_covering ?_ hmem
    intro V g hg
    rw [Sieve.overEquiv_iff]
    have hg' : (⟨g ≫ W.unop.hom, G.map (Over.homMk g rfl :
          Over.mk (g ≫ W.unop.hom) ⟶ W.unop).op x⟩ : Σ φ : V ⟶ U, G.obj (op (Over.mk φ)))
        = ⟨g ≫ W.unop.hom, G.map (Over.homMk g rfl :
            Over.mk (g ≫ W.unop.hom) ⟶ W.unop).op y⟩ := hg
    simpa using hg'

/-- `sheafUnitApp` as a natural transformation `𝟭 ⟶ Φ_sh ⋙ Ψ_sh`: it is natural because
`toSheafify` is. -/
def sheafUnit :
    𝟭 (Sheaf (J.over U) (Type v)) ⟶ sheafFunctorToOver (U := U) J ⋙ sheafFiberFunctor J where
  app G := ObjectProperty.homMk (sheafUnitApp J G.obj)
  naturality G G' η := by
    refine Sheaf.hom_ext ?_
    ext W s
    refine Subtype.ext ?_
    exact (((presheafFunctor (U := U)).map η.hom).comp_app_apply (toSheafify J (presheaf G'.obj))
        (op W.unop.left)
        (⟨W.unop.hom, s⟩ : Σ φ : W.unop.left ⟶ U, G.obj.obj (op (Over.mk φ)))).symm.trans
      ((congrArg (fun α : presheaf G.obj ⟶ sheafify J (presheaf G'.obj) => α.app (op W.unop.left)
          (⟨W.unop.hom, s⟩ : Σ φ : W.unop.left ⟶ U, G.obj.obj (op (Over.mk φ))))
        (toSheafify_naturality J ((presheafFunctor (U := U)).map η.hom))).trans
        ((toSheafify J (presheaf G.obj)).comp_app_apply
          (sheafifyMap J ((presheafFunctor (U := U)).map η.hom)) (op W.unop.left)
          (⟨W.unop.hom, s⟩ : Σ φ : W.unop.left ⟶ U, G.obj.obj (op (Over.mk φ)))))

/-- **The source's `(j_{U!}^{PSh}G)_γ = G` at the sheaf level.** A locally bijective morphism of
sheaves is an isomorphism. -/
instance isIso_sheafUnit_app (G : Sheaf (J.over U) (Type v)) :
    IsIso ((sheafUnit J (U := U)).app G) := by
  rw [← Sheaf.isLocallyBijective_iff_isIso (A := Type v)]
  exact ⟨inferInstanceAs (Presheaf.IsLocallyInjective (J.over U) (sheafUnitApp J G.obj)),
    inferInstanceAs (Presheaf.IsLocallySurjective (J.over U) (sheafUnitApp J G.obj))⟩

/-- A natural transformation whose components are isomorphisms is an isomorphism. -/
instance isIso_sheafUnit : IsIso (sheafUnit J (U := U)) := NatIso.isIso_of_isIso_app _

/-- The unit isomorphism `𝟭 ≅ Φ_sh ⋙ Ψ_sh` of Stacks 00Y1. -/
def sheafUnitIso :
    𝟭 (Sheaf (J.over U) (Type v)) ≅ sheafFunctorToOver (U := U) J ⋙ sheafFiberFunctor J :=
  asIso (sheafUnit J)

/-- The fibre functor `Ψ_sh` is faithful. Two maps `(F, φ) ⟶ (F', φ')` that agree on all fibres
agree: any section `s` of `F` over `X` restricts, on the covering sieve of `X` where `φ(s)` comes
from a morphism `a : V ⟶ U`, to a section of the fibre over `(V, a)`; so the two images of `s`
agree locally, hence agree, `F'` being a sheaf. -/
instance faithful_sheafFiberFunctor : (sheafFiberFunctor (U := U) J).Faithful where
  map_injective := by
    intro T T' f g h
    refine Over.OverMorphism.ext (Sheaf.hom_ext ?_)
    ext X s
    have hsep : Presieve.IsSeparated J T'.left.obj :=
      ((isSheaf_iff_isSheaf_of_type J T'.left.obj).1 T'.left.property).isSeparated
    refine (hsep _ (Presheaf.imageSieve_mem J (toSheafify J (yoneda.obj U))
      (T.hom.hom.app X s))).ext (fun {Y} {k} hk => ?_)
    obtain ⟨a, ha⟩ := hk
    have hmem : T.hom.hom.app (op Y) (T.left.obj.map k.op s)
        = (toSheafify J (yoneda.obj U)).app (op Y) a := by
      rw [NatTrans.naturality_apply T.hom.hom k.op s, ← ha]
    have h' := congrArg (fun m : (sheafFiberFunctor J).obj T ⟶ (sheafFiberFunctor J).obj T' =>
        ((m.hom.app (op (Over.mk a))) (⟨T.left.obj.map k.op s, hmem⟩ :
          ToType (((sheafFiberFunctor J).obj T).obj.obj (op (Over.mk a))))).1) h
    have h'' : f.left.hom.app (op Y) (T.left.obj.map k.op s)
        = g.left.hom.app (op Y) (T.left.obj.map k.op s) := h'
    exact ((NatTrans.naturality_apply f.left.hom k.op s).symm.trans h'').trans
      (NatTrans.naturality_apply g.left.hom k.op s)

/-- `Φ_sh` is faithful, because `Φ_sh ⋙ Ψ_sh` is isomorphic to the identity. -/
instance faithful_sheafFunctorToOver : (sheafFunctorToOver (U := U) J).Faithful :=
  Functor.Faithful.of_comp_iso (sheafUnitIso J).symm

/-- `Φ_sh` is full, because `Φ_sh ⋙ Ψ_sh` is isomorphic to the identity and `Ψ_sh` is faithful. -/
instance full_sheafFunctorToOver : (sheafFunctorToOver (U := U) J).Full :=
  Functor.Full.of_comp_faithful_iso (sheafUnitIso J).symm

/-- **Stacks 00Y1.** The functor `Φ_sh : Sh(C/U) ⥤ Sh(C)/h_U^#` induced by `j_{U!}` is full,
faithful and essentially surjective, i.e. an equivalence. -/
@[stacks 00Y1 "the functor j_{U!} : Sh(C/U) ⥤ Sh(C)/h_U^# is an equivalence"]
instance isEquivalence_sheafFunctorToOver : (sheafFunctorToOver (U := U) J).IsEquivalence where

/-- **Stacks 00Y1**, as an equivalence of categories `Sh(C/U) ≌ Sh(C)/h_U^#`. Its functor is
`sheafFunctorToOver`, the sheaf level `j_{U!}` viewed as a functor into the slice
(`sheafEquivalence_functor`), and its inverse is isomorphic to the fibre functor
`(F, φ) ↦ F_φ`. -/
@[stacks 00Y1 "the resulting equivalence of categories Sh(C/U) ≌ Sh(C)/h_U^#"]
def sheafEquivalence :
    Sheaf (J.over U) (Type v) ≌ Over ((presheafToSheaf J (Type v)).obj (yoneda.obj U)) :=
  (sheafFunctorToOver (U := U) J).asEquivalence

/-- The functor of `sheafEquivalence` is the sheaf level `j_{U!}`, viewed as a functor into the
slice `Sh(C)/h_U^#`. -/
lemma sheafEquivalence_functor :
    (sheafEquivalence (U := U) J).functor = sheafFunctorToOver J :=
  rfl

variable [HasWeakSheafify (J.over U) (Type v)]

section

variable [((Over.forget U).sheafPushforwardContinuous (Type v) (J.over U) J).IsRightAdjoint]

/-- The sheaf underlying `sheafFunctorToOver.obj G` is `j_{U!}G`. This is Stacks 03CD, whiskered by
the inclusion of sheaves into presheaves and simplified using that the sheafification of a sheaf is
itself. -/
def sheafFunctorToOverForgetIso :
    sheafFunctorToOver (U := U) J ⋙ Over.forget _ ≅
      (Over.forget U).sheafPullback (Type v) (J.over U) J :=
  Functor.isoWhiskerLeft (sheafToPresheaf (J.over U) (Type v)) (sheafifyNatIso (U := U) J).symm ≪≫
    Functor.isoWhiskerRight (asIso (sheafificationAdjunction (J.over U) (Type v)).counit)
      ((Over.forget U).sheafPullback (Type v) (J.over U) J)

end

/-- **Stacks 00Y1, in the form the source restates it in**: `j_{U!}` *is* the equivalence
`Φ : Sh(C/U) ≌ Sh(C)/h_U^#` followed by `Over.forget : Sh(C)/h_U^# ⥤ Sh(C)`.

Here `j_{U!}` is an arbitrary left adjoint `L` of the restriction functor `j_U^{-1}`, so this is a
statement about `j_{U!}` rather than about one model of it: `sheafFunctorToOverForgetIso` identifies
`Φ ⋙ Over.forget` with the left adjoint obtained from `Over.forget U`, and two left adjoints of one
functor are canonically isomorphic.

The adjunction `adj` is also what makes that left adjoint exist (`J.overPullback` being the
pushforward along `Over.forget U`), so no adjointness hypothesis beyond `adj` is assumed. -/
@[stacks 00Y1 "j_{U!} is Sh(C/U) ≌ Sh(C)/h_U^# followed by Over.forget, for any left adjoint"]
def sheafFunctorToOverForgetIsoOfAdjunction
    {L : Sheaf (J.over U) (Type v) ⥤ Sheaf J (Type v)} (adj : L ⊣ J.overPullback (Type v) U) :
    sheafFunctorToOver (U := U) J ⋙ Over.forget _ ≅ L :=
  have := adj.isRightAdjoint
  sheafFunctorToOverForgetIso (U := U) J ≪≫
    (adj.leftAdjointUniq ((Over.forget U).sheafAdjunctionContinuous (Type v) (J.over U) J)).symm

end

end CategoryTheory.OverShriek
