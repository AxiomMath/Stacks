module
public import StacksFrontier.CategoryTheory.Sites.Density
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.MorphismDefs
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi
public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Sites.LocalSite
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sites inside a topos, and morphisms of topoi

Three lemmas of the section "Morphisms of topoi" of the Stacks project.

* Let `(C, J)` be a site and let `C' ⊆ Sh(C)` be a full subcategory which contains every
  sheafified representable `h_U^#` and is closed under fibre products in `Sh(C)`. The families
  `{F_i ⟶ F}` of morphisms of `C'` with `∐ F_i ⟶ F` a surjection of sheaves are the coverings of
  a subcanonical Grothendieck topology `K` on `C'`; the functor `v : C ⥤ C'`, `U ↦ h_U^#`, is a
  special cocontinuous functor, so that the morphism of topoi `g : Sh(C) ⟶ Sh(C')` it induces is
  an equivalence; and `g⁻¹ h_F = F` and `g_* F = h_F` for every `F ∈ C'` (Stacks 03A1).
* Every morphism of topoi `f : Sh(C) → Sh(D)` is the composition of the equivalence induced by a
  special cocontinuous functor `v : C ⥤ C'` with the morphism of topoi induced by a morphism of
  sites `u : D ⥤ C'` (Stacks 03A2).
* Every topos `Sh(C)` is equivalent, by a special cocontinuous functor `G : C ⥤ D`, to the topos
  of sheaves on a site `(D, K)` which is subcanonical, has all finite limits, has every subsheaf
  of a representable sheaf representable, and on which `g_*` of each sheaf of a prescribed set is
  representable (Stacks 03CI).

## Main results

* `CategoryTheory.GrothendieckTopology.exists_isDenseSubsite_subcanonical`: Stacks 03A1.
* `MorphismOfTopoi.exists_isDenseSubsite_isMorphismOfSites_pushforward_iso`: Stacks 03A2.
* `GrothendieckTopology.exists_isDenseSubsite_subcanonical_hasFiniteLimits_representable`
  (in the `CategoryTheory` namespace): Stacks 03CI.

## Implementation notes

* A full subcategory of `Sh(C)` with a set of objects is a fully faithful functor
  `ι : C' ⥤ Sh(C)` from a small category `C' : Type max u v`.
* A special cocontinuous functor (Stacks 03CG) is a functor `v` with `Functor.IsDenseSubsite`;
  the equivalence of topoi it induces (Stacks 03A0) is `Functor.IsDenseSubsite.sheafEquiv`.
* The morphism of topoi attached to a cocontinuous functor `v` (Stacks 00XO) has inverse image
  `v.sheafPushforwardContinuous` and pushforward `v.sheafPushforwardCocontinuous`, adjoint by
  `Functor.sheafAdjunctionCocontinuous`.
* A morphism of sites (Stacks 00X1) is the class `IsMorphismOfSites`, which extends
  `Functor.IsContinuous` and asks that the pushforward have a left exact left adjoint; its
  pushforward is `u.sheafPushforwardContinuous` (Stacks 00XC).
* A covering in the sense of 03A1 is stated through a colimit cofan `c` with `IsColimit c`, and a
  surjection of sheaves is `Epi` (`CategoryTheory.Sheaf.isLocallySurjective_iff_epi`).
* Conclusion (2) of Stacks 03CI holds for every Grothendieck topology and is
  `GrothendieckTopology.ofArrows_mem_iff_isLocallySurjective_sigmaDesc_uliftYoneda_map`.

## References

* [Stacks 03A1](https://stacks.math.columbia.edu/tag/03A1)
* [Stacks 03A2](https://stacks.math.columbia.edu/tag/03A2)
* [Stacks 03CI](https://stacks.math.columbia.edu/tag/03CI)
-/

section

universe v u w v₂ u₂
open CategoryTheory Limits
open CategoryTheory Limits Opposite

namespace Stacks.Topos.SiteOfSubcategory

section Reflects

variable {C : Type u} [Category.{v} C] {E : Type u₂} [Category.{v₂} E] {J : GrothendieckTopology C}
  (G : C ⥤ E) (himg : ∀ {U V : C} (g : G.obj U ⟶ G.obj V), G.imageSieve g ∈ J U)
  (heq : ∀ {U V : C} (a b : U ⟶ V), G.map a = G.map b → Sieve.equalizer a b ∈ J U)

include himg in
/-- Local fullness as a criterion for covering: a sieve on `U` is `J`-covering as soon as it
becomes covering after pulling back along every local lift through `G` of a fixed morphism
`g : G(U) ⟶ G(X)`. -/
private lemma mem_of_forall_lift {U X : C} (g : G.obj U ⟶ G.obj X) {T : Sieve U}
    (h : ∀ {W : C} (i : W ⟶ U) (l : W ⟶ X), G.map l = G.map i ≫ g → T.pullback i ∈ J W) :
    T ∈ J U := by
  refine J.transitive (himg g) T ?_
  rintro W i ⟨l, hl⟩
  exact h i l hl

include himg heq in
/-- If `G(a)` lies in the sieve generated by the image of `S`, then the pullback of `S` along `a`
is `J`-covering. -/
private lemma pullback_mem_of_functorPushforward {X U : C} {S : Sieve X} (a : U ⟶ X)
    (ha : S.functorPushforward G (G.map a)) : S.pullback a ∈ J U := by
  obtain ⟨W, c, h, hc, hac⟩ := ha
  refine mem_of_forall_lift G himg h ?_
  intro W' i k hik
  refine J.superset_covering ?_ (heq (i ≫ a) (k ≫ c) ?_)
  · intro W'' m hm
    rw [Sieve.pullback_apply, Sieve.pullback_apply]
    rw [Category.assoc, hm, ← Category.assoc]
    exact S.downward_closed hc (m ≫ k)
  · rw [Functor.map_comp, Functor.map_comp, hac, ← Category.assoc, ← hik]

/-- If morphisms `G(U) ⟶ G(V)` are read as morphisms `h_U^# ⟶ h_V^#` compatibly with composition
and with `G(i) ↦ h_i^#`, then `G` is locally full. -/
private lemma imageSieve_mem_of_hat
    (hat : ∀ U V : C, (G.obj U ⟶ G.obj V) ≃
      ((Sheaf.sheafifiedYoneda J).obj U ⟶ (Sheaf.sheafifiedYoneda J).obj V))
    (hcomp : ∀ {U V W : C} (g : G.obj U ⟶ G.obj V) (h : G.obj V ⟶ G.obj W),
      hat U W (g ≫ h) = hat U V g ≫ hat V W h)
    (hmap : ∀ {U V : C} (i : U ⟶ V), hat U V (G.map i) = (Sheaf.sheafifiedYoneda J).map i)
    {U V : C} (g : G.obj U ⟶ G.obj V) : G.imageSieve g ∈ J U := by
  have h : G.imageSieve g =
      Presheaf.imageSieve (toSheafify J (uliftYoneda.{u}.obj V))
        (Sheaf.sectionEquiv J (hat U V g)) := by
    ext W i
    constructor
    · rintro ⟨l, hl⟩
      refine ⟨ULift.up l, ?_⟩
      rw [← Sheaf.sectionEquiv_sheafifiedYoneda_map, ← hmap, hl, hcomp, hmap,
        Sheaf.sectionEquiv_map_comp]
      rfl
    · rintro ⟨t, ht⟩
      refine ⟨t.down, (hat W V).injective ((Sheaf.sectionEquiv J).injective ?_)⟩
      rw [hmap, hcomp, hmap, Sheaf.sectionEquiv_sheafifiedYoneda_map,
        Sheaf.sectionEquiv_map_comp]
      exact ht
  rw [h]
  exact Presheaf.imageSieve_mem J _ _

/-- Under the hypotheses of `imageSieve_mem_of_hat`, `G` is locally faithful. -/
private lemma equalizer_mem_of_hat
    (hat : ∀ U V : C, (G.obj U ⟶ G.obj V) ≃
      ((Sheaf.sheafifiedYoneda J).obj U ⟶ (Sheaf.sheafifiedYoneda J).obj V))
    (hmap : ∀ {U V : C} (i : U ⟶ V), hat U V (G.map i) = (Sheaf.sheafifiedYoneda J).map i)
    {U V : C} (a b : U ⟶ V) (h : G.map a = G.map b) :
    Sieve.equalizer a b ∈ J U := by
  refine J.superset_covering (fun W i hi => congrArg ULift.down hi)
    (Presheaf.equalizerSieve_mem J (toSheafify J (uliftYoneda.{u}.obj V))
      (ULift.up a : (uliftYoneda.{u}.obj V).obj (op U))
      (ULift.up b : (uliftYoneda.{u}.obj V).obj (op U)) ?_)
  rw [← Sheaf.sectionEquiv_sheafifiedYoneda_map, ← Sheaf.sectionEquiv_sheafifiedYoneda_map,
    ← hmap, ← hmap, h]

end Reflects

/-! ### Subpresheaves of a sheaf of sets -/

section Subsheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Two subpresheaves of a sheaf, each contained in the sheafification of the other, have the same
sheafification. -/
private lemma sheafify_eq_sheafify {P : Cᵒᵖ ⥤ Type w} (hP : Presieve.IsSheaf J P)
    {A B : Subfunctor P} (hAB : A ≤ B.sheafify J) (hBA : B ≤ A.sheafify J) :
    A.sheafify J = B.sheafify J :=
  le_antisymm (Subfunctor.sheafify_le _ _ hAB hP (Subfunctor.sheafify_isSheaf _ hP))
    (Subfunctor.sheafify_le _ _ hBA hP (Subfunctor.sheafify_isSheaf _ hP))

/-- A subpresheaf of a sheaf `T` which is itself a sheaf and contains the range of every leg of a
family `f a : F a ⟶ T` of morphisms of sheaves contains the range of the morphism `∐ F a ⟶ T` the
family induces. -/
private lemma range_desc_le {α : Type w} {F : α → Sheaf J (Type max u v)}
    {T : Sheaf J (Type max u v)} (f : ∀ a, F a ⟶ T) {c : Cofan F} (hc : IsColimit c)
    {A : Subfunctor T.obj} (hA : Presieve.IsSheaf J A.toFunctor)
    (hf : ∀ a, Subfunctor.range (f a).hom ≤ A) :
    Subfunctor.range (Cofan.IsColimit.desc hc f).hom ≤ A := by
  let A' : Sheaf J (Type max u v) :=
    ⟨A.toFunctor, (isSheaf_iff_isSheaf_of_type J _).2 hA⟩
  let incl : A' ⟶ T := ⟨A.ι⟩
  let lift : ∀ a, F a ⟶ A' := fun a => ⟨Subfunctor.lift (f a).hom (hf a)⟩
  have hm : Cofan.IsColimit.desc hc lift ≫ incl = Cofan.IsColimit.desc hc f := by
    refine Cofan.IsColimit.hom_ext hc _ _ fun a => ?_
    rw [← Category.assoc, Cofan.IsColimit.fac, Cofan.IsColimit.fac]
    exact Sheaf.hom_ext (Subfunctor.lift_ι (f a).hom (hf a))
  intro U s hs
  obtain ⟨t, rfl⟩ := hs
  have key :
    (Cofan.IsColimit.desc hc f).hom.app U t =
      incl.hom.app U ((Cofan.IsColimit.desc hc lift).hom.app U t) := by
    conv_lhs => rw [← hm]
    rfl
  rw [key]
  exact ((Cofan.IsColimit.desc hc lift).hom.app U t).2

end Subsheaf

/-! ### The topology -/

section Topology

variable {C : Type u} [Category.{v} C] {D : Type max u v} [SmallCategory D]

/-- The sieve of the arrows `a` of `C` with `v(a) ≫ g` in `S`, pulled back along `i : U' ⟶ U`, is
the sieve of the arrows `b` of `C` with `v(b) ≫ (v(i) ≫ g)` in `S`. -/
private lemma pullback_functorPullback (v : C ⥤ D) {X : D} (S : Sieve X) {U U' : C}
    (g : v.obj U ⟶ X) (i : U' ⟶ U) :
    (Sieve.functorPullback v (S.pullback g)).pullback i =
      Sieve.functorPullback v (S.pullback (v.map i ≫ g)) := by
  ext W b
  simp [Functor.map_comp]

/-- The topology on `C'`: a sieve `S` on `X` covers when, for every `U` in `C` and every
`g : h_U^# ⟶ X`, the arrows of `C` whose image lands in `S ∘ g` form a `J`-covering of `U`. -/
private def top (J : GrothendieckTopology C) (v : C ⥤ D) : GrothendieckTopology D where
  sieves X := {S | ∀ (U : C) (g : v.obj U ⟶ X), Sieve.functorPullback v (S.pullback g) ∈ J U}
  top_mem' X := by
    intro U g
    rw [Sieve.pullback_top, Sieve.functorPullback_top]
    exact J.top_mem U
  pullback_stable' X Y S h hS := by
    intro U g
    rw [← Sieve.pullback_comp]
    exact hS U (g ≫ h)
  transitive' X S hS R hR := by
    intro U g
    refine J.transitive (hS U g) _ ?_
    intro U' a ha
    have h1 := hR (show S (v.map a ≫ g) from ha) U' (𝟙 _)
    rw [Sieve.pullback_id] at h1
    rwa [pullback_functorPullback]

end Topology

section Site

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {D : Type max u v}
  [SmallCategory D] {ι : D ⥤ Sheaf J (Type max u v)} [ι.Full] [ι.Faithful] {v : C ⥤ D}
  (e : v ⋙ ι ≅ Sheaf.sheafifiedYoneda J)

/-- `v` is cover-dense. -/
private lemma isCoverDense (J : GrothendieckTopology C) (v : C ⥤ D) : v.IsCoverDense (top J v)
    where
  is_cover X := by
    intro U g
    have h : Sieve.functorPullback v ((Sieve.coverByImage v X).pullback g) = ⊤ := by
      ext U' a
      simp only [Sieve.functorPullback_apply, Presieve.functorPullback_mem, Sieve.pullback_apply,
        Sieve.top_apply, iff_true]
      exact Presieve.in_coverByImage v (v.map a ≫ g)
    rw [h]
    exact J.top_mem U

/-- `v` is cocontinuous. -/
private lemma isCocontinuous (J : GrothendieckTopology C) (v : C ⥤ D) :
    v.IsCocontinuous J (top J v)
    where
  cover_lift {U} {S} hS := by
    have h := hS U (𝟙 _)
    rwa [Sieve.pullback_id] at h

/-! ### Sections of an object of `C'` -/

/-- Yoneda for sheaves on the subcategory: the morphisms `v(U) ⟶ X` of `C'` are the sections of
`ι(X)` over `U`. -/
private noncomputable def hom (X : D) (U : C) : (v.obj U ⟶ X) ≃ (ι.obj X).obj.obj (op U) where
  toFun g := Sheaf.sectionEquiv J (e.inv.app U ≫ ι.map g)
  invFun s := ι.preimage (e.hom.app U ≫ (Sheaf.sectionEquiv J).symm s)
  left_inv g :=
    ι.map_injective
      (by rw [Functor.map_preimage, Equiv.symm_apply_apply, Iso.hom_inv_id_app_assoc])
  right_inv s := by
    dsimp only
    rw [Functor.map_preimage, Iso.inv_hom_id_app_assoc, Equiv.apply_symm_apply]

private lemma hom_apply {X : D} {U : C} (g : v.obj U ⟶ X) :
    hom e X U g = Sheaf.sectionEquiv J (e.inv.app U ≫ ι.map g) :=
  rfl

/-- Restricting the section of `ι(X)` attached to `g : v(U) ⟶ X` along `i : U' ⟶ U` gives the
section attached to `v(i) ≫ g`. -/
private lemma hom_map {X : D} {U U' : C} (i : U' ⟶ U) (g : v.obj U ⟶ X) :
    (ι.obj X).obj.map i.op (hom e X U g) = hom e X U' (v.map i ≫ g) := by
  rw [hom_apply, hom_apply, ← Sheaf.sectionEquiv_map_comp,
    show ι.map (v.map i ≫ g) = ι.map (v.map i) ≫ ι.map g from ι.map_comp _ _]
  congr 1
  have h : (Sheaf.sheafifiedYoneda J).map i ≫ e.inv.app U = e.inv.app U' ≫ ι.map (v.map i) :=
    e.inv.naturality i
  rw [← Category.assoc, h, Category.assoc]

/-- Composing `g : v(U) ⟶ X` with `k : X ⟶ X'` acts on the corresponding sections by `ι(k)`. -/
private lemma hom_comp {X X' : D} (k : X ⟶ X') {U : C} (g : v.obj U ⟶ X) :
    (ι.map k).hom.app (op U) (hom e X U g) = hom e X' U (g ≫ k) := by
  rw [hom_apply, hom_apply, ← Sheaf.sectionEquiv_comp, ι.map_comp, Category.assoc]

/-! ### `v` is locally fully faithful -/

/-- The bijection between morphisms `v(U) ⟶ v(V)` of `C'` and morphisms `h_U^# ⟶ h_V^#` of
sheafified representables. -/
private noncomputable def hat (U V : C) :
    (v.obj U ⟶ v.obj V) ≃ ((Sheaf.sheafifiedYoneda J).obj U ⟶ (Sheaf.sheafifiedYoneda J).obj V) :=
  (Functor.FullyFaithful.ofFullyFaithful ι).homEquiv.trans ((e.app U).homCongr (e.app V))

private lemma hat_apply {U V : C} (g : v.obj U ⟶ v.obj V) :
    hat e U V g = e.inv.app U ≫ ι.map g ≫ e.hom.app V :=
  rfl

/-- `hat` is compatible with composition. -/
private lemma hat_comp {U V W : C} (g : v.obj U ⟶ v.obj V) (h : v.obj V ⟶ v.obj W) :
    hat e U W (g ≫ h) = hat e U V g ≫ hat e V W h := by
  rw [hat_apply, hat_apply, hat_apply, Functor.map_comp, Category.assoc, Category.assoc,
    Category.assoc, Iso.hom_inv_id_app_assoc]

/-- `hat` takes `v(i)` to `h_i^#`. -/
private lemma hat_v_map {U V : C} (i : U ⟶ V) :
    hat e U V (v.map i) = (Sheaf.sheafifiedYoneda J).map i := by
  rw [hat_apply, show ι.map (v.map i) = (v ⋙ ι).map i from rfl, e.hom.naturality i, ←
    Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

include e in
/-- `v` is locally full. -/
private lemma imageSieve_mem {U V : C} (g : v.obj U ⟶ v.obj V) : v.imageSieve g ∈ J U :=
  imageSieve_mem_of_hat v (hat e) (hat_comp e) (hat_v_map e) g

include e in
/-- `v` is locally faithful. -/
private lemma equalizer_mem {U V : C} (a b : U ⟶ V) (h : v.map a = v.map b) :
    Sieve.equalizer a b ∈ J U :=
  equalizer_mem_of_hat v (hat e) (hat_v_map e) a b h

/-! ### `v` exhibits `(C, J)` as a dense subsite -/

include e in
/-- A sieve of `C` is `J`-covering exactly when the sieve it generates on `v(X)` covers. -/
private lemma functorPushforward_mem_top_iff {X : C} {S : Sieve X} :
    S.functorPushforward v ∈ top J v (v.obj X) ↔ S ∈ J X := by
  constructor
  · intro hS
    refine J.transitive ((isCocontinuous J v).cover_lift hS) S ?_
    intro U a ha
    exact
      pullback_mem_of_functorPushforward v (fun g => imageSieve_mem e g)
        (fun a b h => equalizer_mem e a b h) a ha
  · intro hS U g
    refine mem_of_forall_lift v (fun g => imageSieve_mem e g) g ?_
    intro W i c hic
    refine J.superset_covering ?_ (J.pullback_stable c hS)
    intro W' d hd
    refine ⟨W', d ≫ c, 𝟙 _, hd, ?_⟩
    rw [Functor.map_comp, Category.assoc, ← hic, Category.id_comp, Functor.map_comp]

include e in
/-- `v` exhibits `(C, J)` as a dense subsite of `(C', K)`. -/
private lemma isDenseSubsite : v.IsDenseSubsite J (top J v)
    where
  isCoverDense' := isCoverDense J v
  isLocallyFull' :=
    {
      functorPushforward_imageSieve_mem := fun g =>
        functorPushforward_mem_top_iff e |>.mpr (imageSieve_mem e g) }
  isLocallyFaithful' :=
    {
      functorPushforward_equalizer_mem := fun a b h =>
        functorPushforward_mem_top_iff e |>.mpr (equalizer_mem e a b h) }
  functorPushforward_mem_iff := functorPushforward_mem_top_iff e

/-! ### Coverings of `C'` and surjections of sheaves -/

/-- The subpresheaf of `ι(X)` of the sections whose corresponding morphism of `C'` lies in a sieve
`S` on `X`. -/
private def sub (X : D) (S : Sieve X) : Subfunctor (ι.obj X).obj where
  obj U := {s | ∃ g : v.obj U.unop ⟶ X, S g ∧ hom e X U.unop g = s}
  map := by
    rintro U V i s ⟨g, hg, rfl⟩
    exact ⟨v.map i.unop ≫ g, S.downward_closed hg _, (hom_map e i.unop g).symm⟩

private lemma mem_sub_iff {X : D} (S : Sieve X) {U : C} (s : (ι.obj X).obj.obj (op U)) :
    s ∈ (sub e X S).obj (op U) ↔ S ((hom e X U).symm s) := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    rwa [Equiv.symm_apply_apply]
  · exact fun h => ⟨_, h, (hom e X U).apply_symm_apply s⟩

/-- Restricting a section of `ι(X)` along `i` composes the corresponding morphism of `C'`
with `v(i)`. -/
private lemma hom_symm_map {X : D} {U U' : C} (i : U' ⟶ U) (s : (ι.obj X).obj.obj (op U)) :
    (hom e X U').symm ((ι.obj X).obj.map i.op s) = v.map i ≫ (hom e X U).symm s := by
  obtain ⟨g, rfl⟩ := (hom e X U).surjective s
  rw [hom_map, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- Applying `ι(ψ)` to a section of `ι(Y)` composes the corresponding morphism of `C'` with `ψ`. -/
private lemma hom_symm_comp {X Y : D} (ψ : Y ⟶ X) {U : C} (x : (ι.obj Y).obj.obj (op U)) :
    (hom e X U).symm ((ι.map ψ).hom.app (op U) x) = (hom e Y U).symm x ≫ ψ := by
  obtain ⟨g, rfl⟩ := (hom e Y U).surjective x
  rw [hom_comp, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- Sections of an object `X` of `C'`, viewed as a sheaf on `C`, over `U` are the morphisms
`v(U) ⟶ X` of `C'`. -/
private noncomputable def rho (X : D) : (ι.obj X).obj ≅ v.op ⋙ yoneda.obj X :=
  NatIso.ofComponents (fun U => (hom e X U.unop).symm.toIso)
    (by
      intro U U' m
      ext x
      exact hom_symm_map e m.unop x)

/-- The sieve of a section of `ι(X)` for the subpresheaf cut out by `S` is the sieve of `C` that
appears in the definition of the topology. -/
private lemma sieveOfSection_sub {X : D} (S : Sieve X) {U : C} (g : v.obj U ⟶ X) :
    (sub e X S).sieveOfSection (hom e X U g) = Sieve.functorPullback v (S.pullback g) := by
  refine Sieve.ext fun W i => ?_
  rw [Subfunctor.sieveOfSection_apply, mem_sub_iff, hom_map, Equiv.symm_apply_apply,
    Sieve.functorPullback_apply, Presieve.functorPullback_mem, Sieve.pullback_apply]

include e in
/-- A sieve `S` on `X` covers exactly when the sections of `ι(X)` lying in `S` form a dense
subpresheaf of `ι(X)`. -/
private lemma mem_top_iff_sheafify_eq_top {X : D} (S : Sieve X) :
    S ∈ top J v X ↔ (sub e X S).sheafify J = ⊤ := by
  rw [eq_top_iff, Subfunctor.le_def]
  constructor
  · intro hS U s _
    obtain ⟨g, rfl⟩ := (hom e X U.unop).surjective s
    change (sub e X S).sieveOfSection _ ∈ J _
    rw [sieveOfSection_sub]
    exact hS U.unop g
  · intro h U g
    have h2 : (sub e X S).sieveOfSection (hom e X U g) ∈ J U := h (op U) trivial
    rwa [sieveOfSection_sub] at h2

omit [ι.Full] [ι.Faithful] in
private lemma isSheaf_obj (X : D) : Presieve.IsSheaf J ((ι.obj X).obj) := by
  rw [← isSheaf_iff_isSheaf_of_type]
  exact (ι.obj X).property

/-- The sections of `ι(X)` in the range of `ι(f)`, for a morphism `f : Y ⟶ X` of a sieve `S` on
`X`, lie in the subpresheaf cut out by `S`. -/
private lemma range_map_le_sub {X Y : D} {S : Sieve X} {f : Y ⟶ X} (hf : S f) :
    Subfunctor.range (ι.map f).hom ≤ sub e X S := by
  intro U s hs
  obtain ⟨t, rfl⟩ := hs
  obtain ⟨r, rfl⟩ := (hom e Y U.unop).surjective t
  exact ⟨r ≫ f, S.downward_closed hf r, (hom_comp e f r).symm⟩

/-- Every section of `ι(X)` lying in the sieve generated by a family `p a : Y a ⟶ X` is in the
range of the morphism `∐ ι(Y a) ⟶ ι(X)` the family induces. -/
private lemma sub_ofArrows_le_range {X : D} {α : Type max u v} (Y : α → D) (p : ∀ a, Y a ⟶ X)
    {c : Cofan fun a ↦ ι.obj (Y a)} (hc : IsColimit c) :
    sub e X (Sieve.ofArrows Y p) ≤
      Subfunctor.range (Cofan.IsColimit.desc hc fun a ↦ ι.map (p a)).hom := by
  rintro U s ⟨g, hg, rfl⟩
  obtain ⟨a, r, rfl⟩ := (Sieve.mem_ofArrows_iff Y p g).1 hg
  refine ⟨(c.inj a).hom.app U (hom e (Y a) U.unop r), ?_⟩
  calc
    (Cofan.IsColimit.desc hc fun a ↦ ι.map (p a)).hom.app U
          ((c.inj a).hom.app U (hom e (Y a) U.unop r)) =
        (c.inj a ≫ Cofan.IsColimit.desc hc fun a ↦ ι.map (p a)).hom.app U (hom e (Y a) U.unop r) :=
      rfl
    _ = (ι.map (p a)).hom.app U (hom e (Y a) U.unop r) := by rw [Cofan.IsColimit.fac]
    _ = hom e X U.unop (r ≫ p a) := hom_comp e (p a) r

include e in
/-- A family `{F_i ⟶ F}` of morphisms of `C'` generates a covering sieve exactly when
`∐ F_i ⟶ F` is a surjection of sheaves. -/
private lemma mem_top_iff_epi {X : D} {α : Type max u v} (Y : α → D) (p : ∀ a, Y a ⟶ X)
    {c : Cofan fun a ↦ ι.obj (Y a)} (hc : IsColimit c) :
    Sieve.ofArrows Y p ∈ top J v X ↔ Epi (Cofan.IsColimit.desc hc fun a ↦ ι.map (p a)) := by
  have hX : Presieve.IsSheaf J ((ι.obj X).obj) := isSheaf_obj X
  have hrange :
    Subfunctor.range (Cofan.IsColimit.desc hc fun a ↦ ι.map (p a)).hom ≤
      (sub e X (Sieve.ofArrows Y p)).sheafify J :=
    range_desc_le (fun a ↦ ι.map (p a)) hc (Subfunctor.sheafify_isSheaf _ hX) fun a =>
      (range_map_le_sub e
            ((Sieve.mem_ofArrows_iff Y p (p a)).2 ⟨a, 𝟙 _, (Category.id_comp (p a)).symm⟩)).trans
        (Subfunctor.le_sheafify J _)
  rw [mem_top_iff_sheafify_eq_top e,
    sheafify_eq_sheafify hX ((sub_ofArrows_le_range e Y p hc).trans (Subfunctor.le_sheafify J _))
      hrange]
  exact
    (Presheaf.isLocallySurjective_iff_range_sheafify_eq_top' J
          (Cofan.IsColimit.desc hc fun a ↦ ι.map (p a)).hom).symm.trans
      (Sheaf.isLocallySurjective_iff_epi (Cofan.IsColimit.desc hc fun a ↦ ι.map (p a)))

/-! ### The topology is subcanonical -/

section Families

variable {E : Type u₂} [Category.{v₂} E]

/-- A family of elements depends on its argument alone, not on the proof that the argument lies in
the presieve. -/
private lemma family_congr {P : Eᵒᵖ ⥤ Type w} {X : E} {R : Presieve X}
    (x : Presieve.FamilyOfElements P R) {Y : E} {f f' : Y ⟶ X} (h : f = f') (hf : R f)
    (hf' : R f') : x f hf = x f' hf' := by
  subst h; rfl

/-- A compatible family of morphisms defined on a sieve is compatible with precomposition. -/
private lemma comp_family {X X' : E} {S : Sieve X'}
    {x : Presieve.FamilyOfElements (yoneda.obj X) S.arrows} (hx : x.Compatible) {Y Z : E}
    {f : Y ⟶ X'} (hf : S f) (i : Z ⟶ Y) : i ≫ x f hf = x (i ≫ f) (S.downward_closed hf i) := by
  simpa using hx i (𝟙 Z) hf (S.downward_closed hf i) (by simp)

end Families

/-- The morphism `g : v(U) ⟶ X` corresponding to a section of `ι(X)` lying in the subpresheaf cut
out by a sieve `S` belongs to `S`. -/
private lemma sub_spec {X : D} {S : Sieve X} {U : Cᵒᵖ} (s : (sub e X S).toFunctor.obj U) :
    S ((hom e X U.unop).symm s.1) :=
  (mem_sub_iff e S s.1).1 s.2

/-- The section of `ι(X)` attached to a morphism of `S` lies in the subpresheaf cut out by `S`. -/
private lemma mem_sub {X : D} (S : Sieve X) {U : C} {g : v.obj U ⟶ X} (hg : S g) :
    hom e X U g ∈ (sub e X S).obj (op U) :=
  ⟨g, hg, rfl⟩

/-- The morphism to `ι(X)` from the subpresheaf of `ι(X')` cut out by a sieve `S` on `X'` attached
to a compatible family `x` of morphisms to `X` defined on `S`: it sends the section attached to
`g : v(U) ⟶ X'` in `S` to the section of `ι(X)` attached to `x g`. -/
private noncomputable def familyHom {X X' : D} {S : Sieve X'}
    (x : Presieve.FamilyOfElements (yoneda.obj X) S.arrows) (hx : x.Compatible) :
    (sub e X' S).toFunctor ⟶ (ι.obj X).obj
    where
  app U := ↾fun s ↦ hom e X U.unop (x ((hom e X' U.unop).symm s.1) (sub_spec e s))
  naturality U V i := by
    ext s
    have h1 :
      (hom e X' V.unop).symm ((sub e X' S).toFunctor.map i s).1 =
        v.map i.unop ≫ (hom e X' U.unop).symm s.1 :=
      hom_symm_map e i.unop s.1
    have h2 :=
      (family_congr x h1 (sub_spec e ((sub e X' S).toFunctor.map i s))
            (S.downward_closed (sub_spec e s) (v.map i.unop))).trans
        (comp_family hx (sub_spec e s) (v.map i.unop)).symm
    exact ((hom e X V.unop).congr_arg h2).trans (hom_map e i.unop _).symm

include e in
/-- Two morphisms `v(U) ⟶ X` that agree after precomposition with `v(a)` for every `a` in a
`J`-covering sieve of `U` are equal. -/
private lemma hom_ext_of_mem {X : D} {U : C} {T : Sieve U} (hT : T ∈ J U) {k₁ k₂ : v.obj U ⟶ X}
    (h : ∀ ⦃W : C⦄ (a : W ⟶ U), T a → v.map a ≫ k₁ = v.map a ≫ k₂) : k₁ = k₂ := by
  refine (hom e X U).injective (((isSheaf_obj X T hT).isSeparatedFor.ext ?_))
  intro W a ha
  rw [hom_map, hom_map, h a ha]

/-- Two morphisms `Y ⟶ X` of `C'` are equal as soon as, for every `g : v(U) ⟶ Y`, the sections of
`ι(X)` attached to `g ≫ t₁` and to `g ≫ t₂` agree. -/
private lemma hom_ext {X Y : D} {t₁ t₂ : Y ⟶ X}
    (h : ∀ {U : C} (g : v.obj U ⟶ Y), hom e X U (g ≫ t₁) = hom e X U (g ≫ t₂)) : t₁ = t₂ := by
  refine ι.map_injective (Sheaf.hom_ext ?_)
  ext U s
  obtain ⟨g, rfl⟩ := (hom e Y U.unop).surjective s
  exact (hom_comp e t₁ g).trans ((h g).trans (hom_comp e t₂ g).symm)

include e in
/-- Two morphisms `X' ⟶ X` of `C'` that agree on a covering sieve of `X'` are equal. -/
private lemma hom_ext_of_mem_top {X X' : D} {S : Sieve X'} (hS : S ∈ top J v X') {t₁ t₂ : X' ⟶ X}
    (h : ∀ ⦃Y : D⦄ (f : Y ⟶ X'), S f → f ≫ t₁ = f ≫ t₂) : t₁ = t₂ := by
  refine hom_ext e fun {U} g => (hom e X U).congr_arg (hom_ext_of_mem e (hS U g) ?_)
  intro W a ha
  simpa using h (v.map a ≫ g) ha

include e in
/-- A compatible family `x` of morphisms to `X` defined on a covering sieve `S` of `X'` extends to
a morphism of sheaves `ι(X') ⟶ ι(X)` sending the section attached to a morphism `g` of `S` to the
section attached to `x g`. -/
private lemma exists_hom_app_eq {X X' : D} {S : Sieve X'} (hS : S ∈ top J v X')
    (x : Presieve.FamilyOfElements (yoneda.obj X) S.arrows) (hx : x.Compatible) :
    ∃ φ : (ι.obj X').obj ⟶ (ι.obj X).obj,
      ∀ {U : C} (g : v.obj U ⟶ X') (hg : S g),
        φ.app (op U) (hom e X' U g) = hom e X U (x g hg) := by
  have hden : (sub e X' S).sheafify J = ⊤ := (mem_top_iff_sheafify_eq_top e S).1 hS
  have hle : Subfunctor.range (𝟙 ((ι.obj X').obj)) ≤ (sub e X' S).sheafify J :=
    (Subfunctor.range_id _).le.trans hden.ge
  refine
    ⟨Subfunctor.lift (𝟙 ((ι.obj X').obj)) hle ≫
        (sub e X' S).sheafifyLift (familyHom e x hx) (isSheaf_obj X),
      ?_⟩
  intro U g hg
  refine
    (ConcreteCategory.congr_hom
          (congr_app ((sub e X' S).to_sheafifyLift (familyHom e x hx) (isSheaf_obj X)) (op U))
          (⟨hom e X' U g, mem_sub e S hg⟩ : (sub e X' S).toFunctor.obj (op U))).trans
      ?_
  exact (hom e X U).congr_arg (family_congr x ((hom e X' U).symm_apply_apply g) _ hg)

include e in
/-- A compatible family of morphisms to `X` defined on a covering sieve `S` of `X'` has an
amalgamation. -/
private lemma exists_isAmalgamation {X X' : D} {S : Sieve X'} (hS : S ∈ top J v X')
    (x : Presieve.FamilyOfElements (yoneda.obj X) S.arrows) (hx : x.Compatible) :
    ∃ t : X' ⟶ X, x.IsAmalgamation t := by
  obtain ⟨φ, key⟩ := exists_hom_app_eq e hS x hx
  obtain ⟨t, ht⟩ : ∃ t : X' ⟶ X, ι.map t = (⟨φ⟩ : ι.obj X' ⟶ ι.obj X) :=
    ⟨ι.preimage ⟨φ⟩, ι.map_preimage _⟩
  refine ⟨t, ?_⟩
  intro Y f hf
  simp only [yoneda_obj_map, Quiver.Hom.unop_op]
  refine hom_ext e fun {U} g => ?_
  calc
    hom e X U (g ≫ f ≫ t) = hom e X U ((g ≫ f) ≫ t) := by rw [Category.assoc]
    _ = (ι.map t).hom.app (op U) (hom e X' U (g ≫ f)) := (hom_comp e t (g ≫ f)).symm
    _ = φ.app (op U) (hom e X' U (g ≫ f)) := by rw [ht]
    _ = hom e X U (x (g ≫ f) (S.downward_closed hf g)) := key (g ≫ f) _
    _ = hom e X U (g ≫ x f hf) := (hom e X U).congr_arg (comp_family hx hf g).symm

include e in
/-- The topology on `C'` is subcanonical. -/
private lemma subcanonical : (top J v).Subcanonical := by
  refine GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj _ ?_
  intro X X' S hS x hx
  obtain ⟨t, ht⟩ := exists_isAmalgamation e hS x hx
  refine ⟨t, ht, fun t' ht' => hom_ext_of_mem_top e hS ?_⟩
  intro Y f hf
  exact (ht' f hf).trans (ht f hf).symm

/-- `Θ P` is the presheaf `X ↦ Mor_{Sh(C)}(ι(X), P)` on `C'`, for `P` a sheaf on `C`. -/
private noncomputable abbrev Theta : Sheaf J (Type max u v) ⥤ (Dᵒᵖ ⥤ Type max u v) :=
  yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj ι.op

/-- The sections of a `K`-sheaf `G` on `C'` over `X` are the morphisms of sheaves `ι(X) ⟶ g⁻¹G`
on `C`. -/
private noncomputable def bigEquiv [v.IsDenseSubsite J (top J v)]
    (G : Sheaf (top J v) (Type max u v)) (X : D) :
    G.obj.obj (op X) ≃
      (ι.obj X ⟶ (v.sheafPushforwardContinuous (Type max u v) J (top J v)).obj G) :=
  letI := Functor.IsDenseSubsite.isCoverDense J (top J v) v
  letI := Functor.IsDenseSubsite.isLocallyFull J (top J v) v
  (yonedaEquiv (X := X) (F := G.obj)).symm.trans
    ((Functor.IsCoverDense.restrictHomEquivHom (G := v) (K := top J v) (ℱ := yoneda.obj X)
        (ℱ' := G)).symm.trans
      ((rho e X).homFromEquiv.symm.trans
        ((fullyFaithfulSheafToPresheaf J (Type max u v)).homEquiv (X := ι.obj X)
          (Y := (v.sheafPushforwardContinuous (Type max u v) J (top J v)).obj G)).symm))

/-- The morphism of sheaves `bigEquiv e G X s` sends a section `x` of `ι(X)` over `U` to the
restriction of `s` along the morphism `v(U) ⟶ X` of `C'` that `x` is. -/
private lemma bigEquiv_hom_app [v.IsDenseSubsite J (top J v)]
    (G : Sheaf (top J v) (Type max u v)) (X : D) (s : G.obj.obj (op X)) {U : C}
    (x : (ι.obj X).obj.obj (op U)) :
    (bigEquiv e G X s).hom.app (op U) x = G.obj.map ((hom e X U).symm x).op s :=
  rfl

/-- Naturality of `bigEquiv` in the object `X` of `C'`. -/
private lemma bigEquiv_naturality_obj [v.IsDenseSubsite J (top J v)]
    (G : Sheaf (top J v) (Type max u v)) {X Y : D} (ψ : Y ⟶ X) (s : G.obj.obj (op X)) :
    bigEquiv e G Y (G.obj.map ψ.op s) = ι.map ψ ≫ bigEquiv e G X s := by
  refine Sheaf.hom_ext ?_
  ext ⟨U⟩ x
  dsimp only [TypeCat.Fun.toFun_apply, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app, types_comp_apply]
  rw [bigEquiv_hom_app, bigEquiv_hom_app, hom_symm_comp e ψ x, op_comp, Functor.map_comp_apply]

/-- Naturality of `bigEquiv` in the sheaf `G`. -/
private lemma bigEquiv_naturality_sheaf [v.IsDenseSubsite J (top J v)]
    {G G' : Sheaf (top J v) (Type max u v)} (χ : G ⟶ G') (X : D) (s : G.obj.obj (op X)) :
    bigEquiv e G' X (χ.hom.app (op X) s) =
      bigEquiv e G X s ≫ (v.sheafPushforwardContinuous (Type max u v) J (top J v)).map χ := by
  refine Sheaf.hom_ext ?_
  ext ⟨U⟩ x
  dsimp only [TypeCat.Fun.toFun_apply, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app, types_comp_apply]
  rw [bigEquiv_hom_app, bigEquiv_hom_app]
  exact (types_congr_hom (χ.hom.naturality ((hom e X U).symm x).op) s).symm

/-- `bigEquiv` as a natural isomorphism in both variables. -/
private noncomputable def natA [v.IsDenseSubsite J (top J v)] :
    sheafToPresheaf (top J v) (Type max u v) ≅
    v.sheafPushforwardContinuous (Type max u v) J (top J v) ⋙ Theta (ι := ι) :=
  NatIso.ofComponents
    (fun G =>
      NatIso.ofComponents (fun X => Equiv.toIso (bigEquiv e G X.unop))
        (by
          intro X Y m
          ext s
          exact bigEquiv_naturality_obj e G m.unop s))
    (by
      intro G G' χ
      ext X s
      exact bigEquiv_naturality_sheaf e χ X.unop s)

section Conclusions

variable [(top J v).Subcanonical] [v.IsDenseSubsite J (top J v)]

include e in
/-- The sheaf on `C` underlying the representable sheaf `h_X` on `C'` is `ι(X)`. -/
private noncomputable def natFourApp (X : D) :
    ((top J v).yoneda ⋙ v.sheafPushforwardContinuous (Type max u v) J (top J v)).obj X ≅ ι.obj X :=
  (fullyFaithfulSheafToPresheaf J (Type max u v)).preimageIso
    (NatIso.ofComponents (fun U => Equiv.toIso (hom e X U.unop))
      (by
        intro U U' m
        ext g
        exact (hom_map e m.unop g).symm))

include e in
/-- `g⁻¹ h_F = F` for every object `F` of `C'`. -/
private noncomputable def natFour :
    (top J v).yoneda ⋙ v.sheafPushforwardContinuous (Type max u v) J (top J v) ≅ ι :=
  NatIso.ofComponents (natFourApp e)
    (by
      intro X X' k
      refine Sheaf.hom_ext ?_
      ext U g
      exact (hom_comp e k g).symm)

include e in
/-- `g_* F = h_F` for every object `F` of `C'`. -/
private noncomputable def natFive :
    ι ⋙ v.sheafPushforwardCocontinuous (Type max u v) J (top J v) ≅ (top J v).yoneda :=
  Functor.isoWhiskerRight (natFour e).symm
      (v.sheafPushforwardCocontinuous (Type max u v) J (top J v)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (top J v).yoneda
      (asIso (v.sheafAdjunctionCocontinuous (Type max u v) J (top J v)).unit).symm ≪≫
    (top J v).yoneda.rightUnitor

end Conclusions

end Site

end Stacks.Topos.SiteOfSubcategory

namespace CategoryTheory.GrothendieckTopology

@[expose] public section

open Stacks.Topos.SiteOfSubcategory in
/-- Let `(C, J)` be a site and let `ι : C' ⥤ Sh(C)` be a full subcategory of the
category of sheaves of sets on `C`, with a set of objects, which is closed under fibre products
and contains the sheafified representables: `v : C ⥤ C'` is a functor with `v ⋙ ι ≅ h_{-}^#`.
Declare a covering of `C'` to be a family `{F_i ⟶ F}` of morphisms with `∐ F_i ⟶ F` a surjection
of sheaves. Then

1. these coverings are the coverings of a Grothendieck topology `K` on `C'`, i.e. `C'` is a site;
2. `K` is subcanonical, i.e. representable presheaves on `C'` are sheaves;
3. `v` is a special cocontinuous functor, i.e. `v.IsDenseSubsite J K`, hence the induced morphism
   of topoi `g : Sh(C) ⟶ Sh(C')` is an equivalence;
4. `g⁻¹ h_F = F` for every object `F` of `C'`; and
5. `g_* F = h_F` for every object `F` of `C'`; along `v` this is
   `g_* h_U^# = h_{v U} = h_{h_U^#}`. -/
@[stacks 03A1 "A full subcategory of `Sh(C)` with a set of objects which contains the sheafified
  representables and is closed under fibre products is a site, for the coverings whose coproduct
  is a surjection of sheaves; that site is subcanonical, `U ↦ h_U^#` is a special cocontinuous
  functor, and the induced equivalence of topoi matches the representables of the two sides. This
  is all five conclusions, with (5) stated for every object of the subcategory."]
public theorem exists_isDenseSubsite_subcanonical {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) {D : Type max u v} [SmallCategory D]
    (ι : D ⥤ Sheaf J (Type max u v)) [ι.Full] [ι.Faithful] [HasPullbacks D]
    [PreservesLimitsOfShape WalkingCospan ι] (v : C ⥤ D) (e : v ⋙ ι ≅ Sheaf.sheafifiedYoneda J) :
    ∃ K : GrothendieckTopology D,
      (∀ {X : D} {α : Type max u v} (Y : α → D) (p : ∀ a, Y a ⟶ X) {c : Cofan fun a ↦ ι.obj (Y a)}
          (hc : IsColimit c),
          Sieve.ofArrows Y p ∈ K X ↔ Epi (Cofan.IsColimit.desc hc fun a ↦ ι.map (p a))) ∧
        ∃ (_ : K.Subcanonical) (_ : v.IsDenseSubsite J K),
          Nonempty (K.yoneda ⋙ v.sheafPushforwardContinuous (Type max u v) J K ≅ ι) ∧
            Nonempty (ι ⋙ v.sheafPushforwardCocontinuous (Type max u v) J K ≅ K.yoneda) := by
  let hs := subcanonical e
  let hd := isDenseSubsite e
  refine ⟨top J v, ?_, hs, hd, ⟨natFour e⟩, ⟨natFive e⟩⟩
  intro X α Y p c hc
  exact mem_top_iff_epi e Y p hc

end

end CategoryTheory.GrothendieckTopology

end

/-!
## Every morphism of topoi comes from a morphism of sites

For a morphism of topoi `f : Sh(C) → Sh(D)`, the site `C'` is the full subcategory of `Sh(C)` on
the sheafified representables `h_U^#` for `U ∈ C` and the sheaves `f⁻¹h_V^#` for `V ∈ D`, with
the sheaf-surjective families as coverings; `v` is `U ↦ h_U^#` and `u` is `V ↦ f⁻¹h_V^#`.
-/

section

universe v₁ u₁ v₂ u₂
open CategoryTheory Limits
open CategoryTheory Limits Opposite

namespace Stacks.Topos.MorphismFactorization

section Reflects

variable {C : Type u₁} [Category.{v₁} C] {E : Type u₂} [Category.{v₂} E]
  {J : GrothendieckTopology C} (G : C ⥤ E)
  (himg : ∀ {U V : C} (g : G.obj U ⟶ G.obj V), G.imageSieve g ∈ J U)
  (heq : ∀ {U V : C} (a b : U ⟶ V), G.map a = G.map b → Sieve.equalizer a b ∈ J U)

include himg in
/-- If `S` is `J`-covering, then so is the sieve of arrows of `C` whose image lies in the pullback
along `g : G(U) ⟶ G(X)` of the sieve generated by the image of `S`. -/
private lemma functorPullback_pullback_functorPushforward_mem {X U : C} {S : Sieve X}
    (hS : S ∈ J X) (g : G.obj U ⟶ G.obj X) :
    Sieve.functorPullback G ((S.functorPushforward G).pullback g) ∈ J U := by
  refine Stacks.Topos.SiteOfSubcategory.mem_of_forall_lift G himg g ?_
  intro W i c hic
  refine J.superset_covering ?_ (J.pullback_stable c hS)
  intro W' d hd
  refine ⟨W', d ≫ c, 𝟙 _, hd, ?_⟩
  rw [Functor.map_comp, Category.assoc, ← hic, Category.id_comp, Functor.map_comp]

include himg heq in
/-- A sieve of `C` is `J`-covering as soon as the sieve it generates on `G(X)` pulls back to a
`J`-covering sieve of `X`. -/
private lemma mem_of_functorPullback_functorPushforward_mem {X : C} {S : Sieve X}
    (h : Sieve.functorPullback G (S.functorPushforward G) ∈ J X) : S ∈ J X :=
  J.transitive h S fun _ a ha =>
    Stacks.Topos.SiteOfSubcategory.pullback_mem_of_functorPushforward G himg heq a ha

end Reflects

/-! ### The site `C'` -/

section Site

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₁} [Category.{v₁} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (f : MorphismOfTopoi (Sheaf J (Type max u₁ v₁)) (Sheaf K (Type max u₁ v₁)))

/-- The objects of the site `C'`: the sheafified representables `h_U^#` for `U` in `C`, and the
inverse images `f⁻¹h_V^#` for `V` in `D`. -/
@[reducible]
private noncomputable def emb : ULift.{v₁} (C ⊕ D) → Sheaf J (Type max u₁ v₁)
  | ⟨.inl U⟩ => (Sheaf.sheafifiedYoneda J).obj U
  | ⟨.inr V⟩ => f.inverseImage.obj ((Sheaf.sheafifiedYoneda K).obj V)

/-- The site `C'`: the full subcategory of `Sh(C)` on the objects `emb f`. -/
private noncomputable abbrev Site : Type max u₁ v₁ :=
  InducedCategory (Sheaf J (Type max u₁ v₁)) (emb f)

/-- The inclusion `C' ⥤ Sh(C)`, a fully faithful functor. -/
private noncomputable abbrev incl : Site f ⥤ Sheaf J (Type max u₁ v₁) :=
  inducedFunctor (emb f)

/-- The functor `v : C ⥤ C'`, `U ↦ h_U^#`. -/
private noncomputable def vv : C ⥤ Site f where
  obj U := ULift.up (Sum.inl U)
  map i := InducedCategory.homMk ((Sheaf.sheafifiedYoneda J).map i)
  map_id U := InducedCategory.hom_ext ((Sheaf.sheafifiedYoneda J).map_id U)
  map_comp i j := InducedCategory.hom_ext ((Sheaf.sheafifiedYoneda J).map_comp i j)

/-- The functor `u : D ⥤ C'`, `V ↦ f⁻¹h_V^#`. -/
private noncomputable def uu : D ⥤ Site f where
  obj V := ULift.up (Sum.inr V)
  map k := InducedCategory.homMk (f.inverseImage.map ((Sheaf.sheafifiedYoneda K).map k))
  map_id V := by
    apply InducedCategory.hom_ext
    rw [InducedCategory.homMk_hom, InducedCategory.id_hom, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_id]
  map_comp k k' := by
    apply InducedCategory.hom_ext
    rw [InducedCategory.homMk_hom, InducedCategory.comp_hom, InducedCategory.homMk_hom,
      InducedCategory.homMk_hom, Functor.map_comp, Functor.map_comp]

/-- The topology on `C'`: a sieve `S` on `X` covers when, for every `U` in `C` and every
`g : h_U^# ⟶ X`, the arrows of `C` whose image lands in `S ∘ g` form a `J`-covering of `U`. -/
private noncomputable abbrev top : GrothendieckTopology (Site f) :=
  Stacks.Topos.SiteOfSubcategory.top J (vv f)

/-- `v` is cover-dense. -/
private lemma isCoverDense_vv : (vv f).IsCoverDense (top f) :=
  Stacks.Topos.SiteOfSubcategory.isCoverDense J (vv f)

/-! ### `v` is locally fully faithful -/

/-- `v` is locally full. -/
private lemma imageSieve_vv_mem {U V : C} (g : (vv f).obj U ⟶ (vv f).obj V) :
    (vv f).imageSieve g ∈ J U :=
  Stacks.Topos.SiteOfSubcategory.imageSieve_mem_of_hat (vv f)
    (fun _ _ => InducedCategory.homEquiv) (fun _ _ => rfl) (fun _ => rfl) g

/-- `v` is locally faithful. -/
private lemma equalizer_vv_mem {U V : C} (a b : U ⟶ V) (h : (vv f).map a = (vv f).map b) :
    Sieve.equalizer a b ∈ J U :=
  Stacks.Topos.SiteOfSubcategory.equalizer_mem_of_hat (vv f)
    (fun _ _ => InducedCategory.homEquiv) (fun _ => rfl) a b h

/-! ### `v` exhibits `(C, J)` as a dense subsite of `(C', J')` -/

/-- A sieve of `C` is `J`-covering exactly when the sieve it generates on `v(X)` is
`J'`-covering. -/
private lemma functorPushforward_mem_top_iff {X : C} {S : Sieve X} :
    S.functorPushforward (vv f) ∈ top f ((vv f).obj X) ↔ S ∈ J X := by
  refine ⟨fun hS => ?_, fun hS U g => ?_⟩
  · refine mem_of_functorPullback_functorPushforward_mem (vv f) (imageSieve_vv_mem f)
      (equalizer_vv_mem f) ?_
    simpa using hS X (𝟙 _)
  · exact functorPullback_pullback_functorPushforward_mem (vv f) (imageSieve_vv_mem f) hS g

private lemma isLocallyFull_vv : (vv f).IsLocallyFull (top f)
    where
  functorPushforward_imageSieve_mem g :=
    (functorPushforward_mem_top_iff f).mpr (imageSieve_vv_mem f g)

private lemma isLocallyFaithful_vv : (vv f).IsLocallyFaithful (top f)
    where
  functorPushforward_equalizer_mem a b h :=
    (functorPushforward_mem_top_iff f).mpr (equalizer_vv_mem f a b h)

private lemma isDenseSubsite_vv : (vv f).IsDenseSubsite J (top f)
    where
  isCoverDense' := isCoverDense_vv f
  isLocallyFull' := isLocallyFull_vv f
  isLocallyFaithful' := isLocallyFaithful_vv f
  functorPushforward_mem_iff := functorPushforward_mem_top_iff f

/-! ### `u` commutes with fibre products and with the final object -/

private lemma uu_comp_incl : uu f ⋙ incl f = Sheaf.sheafifiedYoneda K ⋙ f.inverseImage :=
  rfl

/-- `u` preserves finite limits, in particular fibre products and the final object. -/
private lemma preservesFiniteLimits_uu : PreservesFiniteLimits (uu f) := by
  have : PreservesFiniteLimits f.inverseImage := f.preservesFiniteLimits
  have : PreservesFiniteLimits (Sheaf.sheafifiedYoneda K) :=
    inferInstanceAs (PreservesFiniteLimits (uliftYoneda.{u₁} ⋙ presheafToSheaf K _))
  have : PreservesFiniteLimits (uu f ⋙ incl f) := by
    rw [uu_comp_incl]
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves (uu f) (incl f)

/-! ### `u` is continuous and defines a morphism of sites -/

/-- Restricting a section of `f_*H` along `k : V' ⟶ V` corresponds, under the adjunction
`f⁻¹ ⊣ f_*` followed by Yoneda for sheaves on `D`, to precomposition with `f⁻¹h_k^#`. -/
private lemma sectionEquiv_homEquiv_map_comp {H : Sheaf J (Type max u₁ v₁)} {V V' : D} (k : V' ⟶ V)
    (φ : f.inverseImage.obj ((Sheaf.sheafifiedYoneda K).obj V) ⟶ H) :
    Sheaf.sectionEquiv K
        (f.adj.homEquiv ((Sheaf.sheafifiedYoneda K).obj V') H
          (f.inverseImage.map ((Sheaf.sheafifiedYoneda K).map k) ≫ φ)) =
      (f.pushforward.obj H).obj.map k.op
        (Sheaf.sectionEquiv K (f.adj.homEquiv ((Sheaf.sheafifiedYoneda K).obj V) H φ)) := by
  rw [Adjunction.homEquiv_naturality_left, Sheaf.sectionEquiv_map_comp]

/-- The action of `ψ : H ⟶ H'` on the sections of `f_*H` corresponds, under the same
identification, to postcomposition with `ψ`. -/
private lemma sectionEquiv_homEquiv_comp {H H' : Sheaf J (Type max u₁ v₁)} (ψ : H ⟶ H') {V : D}
    (φ : f.inverseImage.obj ((Sheaf.sheafifiedYoneda K).obj V) ⟶ H) :
    Sheaf.sectionEquiv K (f.adj.homEquiv ((Sheaf.sheafifiedYoneda K).obj V) H' (φ ≫ ψ)) =
      (f.pushforward.map ψ).hom.app (op V)
        (Sheaf.sectionEquiv K (f.adj.homEquiv ((Sheaf.sheafifiedYoneda K).obj V) H φ)) := by
  rw [Adjunction.homEquiv_naturality_right, Sheaf.sectionEquiv_comp]

/-- Yoneda for sheaves on `D` together with the adjunction `f⁻¹ ⊣ f_*`: the presheaf
`V ↦ Mor_{Sh(C)}(f⁻¹h_V^#, H)` on `D` is `f_*H`, naturally in the sheaf `H` on `C`. -/
private noncomputable def natB :
    yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj (Sheaf.sheafifiedYoneda K ⋙ f.inverseImage).op ≅
      f.pushforward ⋙ sheafToPresheaf K (Type max u₁ v₁) :=
  NatIso.ofComponents
    (fun H =>
      NatIso.ofComponents
        (fun V =>
          Equiv.toIso
            ((f.adj.homEquiv ((Sheaf.sheafifiedYoneda K).obj V.unop) H).trans
              (Sheaf.sectionEquiv K)))
        (by
          intro V V' k
          ext φ
          exact sectionEquiv_homEquiv_map_comp f k.unop φ))
    (by
      intro H H' ψ
      ext V φ
      exact sectionEquiv_homEquiv_comp f ψ φ)

section DenseSubsite

variable [inst : (vv f).IsDenseSubsite J (top f)]

/-- The inverse image `g⁻¹ : Sh(C') ⥤ Sh(C)` of the morphism of topoi attached to `v`. -/
private noncomputable abbrev gInv : Sheaf (top f) (Type max u₁ v₁) ⥤ Sheaf J (Type max u₁ v₁) :=
  (vv f).sheafPushforwardContinuous (Type max u₁ v₁) J (top f)

/-- The pushforward `g_* : Sh(C) ⥤ Sh(C')` of the morphism of topoi attached to `v`. -/
private noncomputable abbrev gStar : Sheaf J (Type max u₁ v₁) ⥤ Sheaf (top f) (Type max u₁ v₁) :=
  (vv f).sheafPushforwardCocontinuous (Type max u₁ v₁) J (top f)

omit inst in
/-- The functor `v : C ⥤ C'` followed by the inclusion is `U ↦ h_U^#`. -/
private noncomputable def vvIncl : vv f ⋙ incl f ≅ Sheaf.sheafifiedYoneda J := Iso.refl _

/-- `bigEquiv` as a natural isomorphism in both variables. -/
private noncomputable def natA :
    sheafToPresheaf (top f) (Type max u₁ v₁) ≅
      gInv f ⋙ Stacks.Topos.SiteOfSubcategory.Theta (ι := incl f) :=
  Stacks.Topos.SiteOfSubcategory.natA (vvIncl f)

/-- For a `J'`-sheaf `G` on `C'`, the presheaf `V ↦ G(f⁻¹h_V^#)` on `D` is the pushforward
`f_*(g⁻¹G)`. -/
private noncomputable def secIso (G : Sheaf (top f) (Type max u₁ v₁)) :
    (uu f).op ⋙ G.obj ≅ (f.pushforward.obj ((gInv f).obj G)).obj :=
  Functor.isoWhiskerLeft (uu f).op ((natA f).app G) ≪≫ (natB f).app ((gInv f).obj G)

private lemma isContinuous_uu : (uu f).IsContinuous K (top f)
    where
  op_comp_isSheaf_of_types G :=
    (isSheaf_iff_isSheaf_of_type K _).1
      ((Presheaf.isSheaf_of_iso_iff (secIso f G)).mpr
        (f.pushforward.obj ((gInv f).obj G)).property)

/-- The natural isomorphism `u^s ≅ g⁻¹ ⋙ f_*`, the functorial form of `secIso`. -/
private noncomputable def Phi :
    letI := isContinuous_uu f
    (uu f).sheafPushforwardContinuous (Type max u₁ v₁) K (top f) ≅ gInv f ⋙ f.pushforward :=
  letI := isContinuous_uu f
  Functor.fullyFaithfulCancelRight (sheafToPresheaf K (Type max u₁ v₁))
    (Functor.isoWhiskerRight (natA f) ((Functor.whiskeringLeft _ _ _).obj (uu f).op) ≪≫
      Functor.isoWhiskerLeft (gInv f) (natB f) ≪≫
      (Functor.associator (gInv f) f.pushforward (sheafToPresheaf K (Type max u₁ v₁))).symm)

private lemma isMorphismOfSites_uu : _root_.IsMorphismOfSites.{max u₁ v₁} (uu f) K (top f) := by
  let := isContinuous_uu f
  let e := (gInv f).asEquivalence
  have hadj : f.inverseImage ⋙ e.inverse ⊣ gInv f ⋙ f.pushforward := f.adj.comp e.symm.toAdjunction
  have i1 : PreservesFiniteLimits f.inverseImage := f.preservesFiniteLimits
  exact
    { __ := isContinuous_uu f
      hasExactLeftAdjoint :=
        ⟨f.inverseImage ⋙ e.inverse, ⟨hadj.ofNatIsoRight (Phi f).symm⟩,
          comp_preservesFiniteLimits _ _⟩ }

/-- `f_*` is the composition of `g_*` with `u^s`. -/
private noncomputable def factorIso :
    letI := isContinuous_uu f
    f.pushforward ≅ gStar f ⋙ (uu f).sheafPushforwardContinuous (Type max u₁ v₁) K (top f) := by
  letI := isContinuous_uu f
  letI adjG := (vv f).sheafAdjunctionCocontinuous (Type max u₁ v₁) J (top f)
  haveI : IsIso adjG.counit := NatIso.isIso_of_isIso_app _
  exact
    f.pushforward.leftUnitor.symm ≪≫
      Functor.isoWhiskerRight (asIso adjG.counit).symm f.pushforward ≪≫
      Functor.associator (gStar f) (gInv f) f.pushforward ≪≫
      Functor.isoWhiskerLeft (gStar f) (Phi f).symm

end DenseSubsite

end Site

end Stacks.Topos.MorphismFactorization

namespace MorphismOfTopoi

@[expose] public section

open Stacks.Topos.MorphismFactorization in
/-- Let `(C, J)` and `(D, K)` be sites and let `f : Sh(C) → Sh(D)` be a morphism
of topoi. Then there are a site `(C', J')` and functors `v : C ⥤ C'` and `u : D ⥤ C'` such that

1. `v` is a special cocontinuous functor, i.e. exhibits `(C, J)` as a dense subsite of
   `(C', J')`, so that the morphism of topoi `g : Sh(C) → Sh(C')` it induces is an equivalence;
2. `u` commutes with fibre products *and with the final object*, is continuous, and defines a
   morphism of sites `C' → D`, hence a morphism of topoi `h : Sh(C') → Sh(D)`; and
3. `f` agrees with `h ∘ g`, in the sense that `f_*` is isomorphic to the composition of the
   pushforwards `g_* = v.sheafPushforwardCocontinuous` and `h_* = u.sheafPushforwardContinuous`.
-/
@[stacks 03A2 "Every morphism of topoi is the composition of the equivalence induced by a special
  cocontinuous functor with the morphism of topoi induced by a morphism of sites. The conclusion
  also records, from Stacks 03CJ, that `u` preserves the final object."]
public theorem exists_isDenseSubsite_isMorphismOfSites_pushforward_iso {C : Type u₁}
    [Category.{v₁} C] {D : Type u₁} [Category.{v₁} D] {J : GrothendieckTopology C}
    {K : GrothendieckTopology D}
    (f : MorphismOfTopoi (Sheaf J (Type max u₁ v₁)) (Sheaf K (Type max u₁ v₁))) :
    ∃ (C' : Type max u₁ v₁) (_ : SmallCategory C') (J' : GrothendieckTopology C') (v : C ⥤ C') (u :
      D ⥤ C') (_ : v.IsDenseSubsite J J') (_ : _root_.IsMorphismOfSites.{max u₁ v₁} u K J'),
      PreservesLimitsOfShape WalkingCospan u ∧
        PreservesLimitsOfShape (Discrete PEmpty.{1}) u ∧
          Nonempty
            (f.pushforward ≅
              v.sheafPushforwardCocontinuous (Type max u₁ v₁) J J' ⋙
                u.sheafPushforwardContinuous (Type max u₁ v₁) K J') := by
  let inst := isDenseSubsite_vv f
  have := preservesFiniteLimits_uu f
  exact
    ⟨Site f, inferInstance, top f, vv f, uu f, inst, isMorphismOfSites_uu f,
      inferInstance, inferInstance, ⟨factorIso f⟩⟩

end

end MorphismOfTopoi

end

/-!
## Every topos is the topos of sheaves on a site with all finite limits

For a site `(C, J)` and a family of sheaves `F i`, the site `D` is the full subcategory of
`Sh(C)` on the sheafified representables `h_U^#`, the sheaves `F i`, and the subsheaves of finite
products of these, with the sheaf-surjective families as coverings; `G` is `U ↦ h_U^#`.
-/

section

universe v u
open CategoryTheory Limits
open CategoryTheory Limits Opposite

namespace Stacks.Topos.GoodSitePresentation

section Yoneda

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The sheafified Yoneda embedding `U ↦ h_U^#`. -/
private noncomputable abbrev shY : C ⥤ Sheaf J (Type max u v) :=
  uliftYoneda.{u} ⋙ presheafToSheaf J (Type max u v)

variable {J}

end Yoneda

/-! ### The generators and the ambient products -/

/-- Formal finite products of generators: `nil` is the empty product, i.e. the final sheaf,
`leaf` is a generator and `node` is a binary product. -/
private inductive Amb (C : Type u) (I : Type max u v) : Type max u v
  | nil : Amb C I
  | leaf : ULift.{v} C ⊕ I → Amb C I
  | node : Amb C I → Amb C I → Amb C I

section Site

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {I : Type max u v}
  (F : I → Sheaf J (Type max u v))

/-- The generating sheaves: the sheafified representables `h_U^#` and the given sheaves `F i`. -/
@[reducible]
private noncomputable def gen : ULift.{v} C ⊕ I → Sheaf J (Type max u v)
  | .inl U => (shY J).obj U.down
  | .inr i => F i

/-- The sheaf underlying a formal finite product of generators. -/
private noncomputable def ambSheaf : Amb C I → Sheaf J (Type max u v)
  | .nil => ⊤_ (Sheaf J (Type max u v))
  | .leaf g => gen F g
  | .node s t => ambSheaf s ⨯ ambSheaf t

/-- The empty ambient product is a final sheaf. -/
private noncomputable def isTerminalAmbSheafNil : IsTerminal (ambSheaf F (Amb.nil : Amb C I)) :=
  terminalIsTerminal

/-- The sheafification of a subfunctor of the presheaf underlying a sheaf is a sheaf. -/
private lemma isSheaf_sheafify {P : Sheaf J (Type max u v)} (S : Subfunctor P.obj) :
    Presheaf.IsSheaf J (S.sheafify J).toFunctor :=
  (isSheaf_iff_isSheaf_of_type _ _).2
    (S.sheafify_isSheaf ((isSheaf_iff_isSheaf_of_type _ _).1 P.property))

/-- The objects of the site: a generator, or a subsheaf of an ambient product of generators. -/
private noncomputable abbrev Idx : Type max u v :=
  (ULift.{v} C ⊕ I) ⊕ Σ t : Amb C I, Subfunctor (ambSheaf F t).obj

/-- The objects of the site, as sheaves on `C`. -/
@[reducible]
private noncomputable def emb : Idx F → Sheaf J (Type max u v)
  | .inl g => gen F g
  | .inr ⟨_, S⟩ => ⟨(S.sheafify J).toFunctor, isSheaf_sheafify S⟩

/-- The site `D`: the full subcategory of `Sh(C)` on the objects `emb F`. -/
private noncomputable abbrev Site : Type max u v :=
  InducedCategory (Sheaf J (Type max u v)) (emb F)

/-- The inclusion `D ⥤ Sh(C)`, a fully faithful functor. -/
private noncomputable abbrev incl : Site F ⥤ Sheaf J (Type max u v) :=
  inducedFunctor (emb F)

/-- The functor `G : C ⥤ D`, `U ↦ h_U^#`. -/
private noncomputable def vv : C ⥤ Site F where
  obj U := Sum.inl (Sum.inl (ULift.up U))
  map i := InducedCategory.homMk ((shY J).map i)
  map_id U := InducedCategory.hom_ext ((shY J).map_id U)
  map_comp i j := InducedCategory.hom_ext ((shY J).map_comp i j)

/-- The topology on `D`: a sieve `S` on `X` covers when, for every `U` in `C` and every
`g : h_U^# ⟶ X`, the arrows of `C` whose image lands in `S ∘ g` form a `J`-covering of `U`. -/
private noncomputable abbrev top : GrothendieckTopology (Site F) :=
  Stacks.Topos.SiteOfSubcategory.top J (vv F)

private lemma isCoverDense_vv : (vv F).IsCoverDense (top F) :=
  Stacks.Topos.SiteOfSubcategory.isCoverDense J (vv F)

/-! ### Local fullness and faithfulness of `G` -/

private lemma imageSieve_vv_mem {U V : C} (g : (vv F).obj U ⟶ (vv F).obj V) :
    (vv F).imageSieve g ∈ J U :=
  Stacks.Topos.SiteOfSubcategory.imageSieve_mem_of_hat (vv F)
    (fun _ _ => InducedCategory.homEquiv) (fun _ _ => rfl) (fun _ => rfl) g

private lemma equalizer_vv_mem {U V : C} (a b : U ⟶ V) (h : (vv F).map a = (vv F).map b) :
    Sieve.equalizer a b ∈ J U :=
  Stacks.Topos.SiteOfSubcategory.equalizer_mem_of_hat (vv F)
    (fun _ _ => InducedCategory.homEquiv) (fun _ => rfl) a b h

/-! ### `G` exhibits `(C, J)` as a dense subsite of `(D, K)` -/

private lemma functorPushforward_mem_top_iff {X : C} {S : Sieve X} :
    S.functorPushforward (vv F) ∈ top F ((vv F).obj X) ↔ S ∈ J X := by
  refine ⟨fun hS => ?_, fun hS U g => ?_⟩
  · refine Stacks.Topos.MorphismFactorization.mem_of_functorPullback_functorPushforward_mem (vv F)
      (imageSieve_vv_mem F) (equalizer_vv_mem F) ?_
    simpa using hS X (𝟙 _)
  · exact Stacks.Topos.MorphismFactorization.functorPullback_pullback_functorPushforward_mem
      (vv F) (imageSieve_vv_mem F) hS g

private lemma isLocallyFull_vv : (vv F).IsLocallyFull (top F)
    where
  functorPushforward_imageSieve_mem g :=
    (functorPushforward_mem_top_iff F).mpr (imageSieve_vv_mem F g)

private lemma isLocallyFaithful_vv : (vv F).IsLocallyFaithful (top F)
    where
  functorPushforward_equalizer_mem a b h :=
    (functorPushforward_mem_top_iff F).mpr (equalizer_vv_mem F a b h)

private lemma isDenseSubsite_vv : (vv F).IsDenseSubsite J (top F)
    where
  isCoverDense' := isCoverDense_vv F
  isLocallyFull' := isLocallyFull_vv F
  isLocallyFaithful' := isLocallyFaithful_vv F
  functorPushforward_mem_iff := functorPushforward_mem_top_iff F

/-! ### Closure of the site under subsheaves, and its finite limits -/

/-- Every object of the site is a subsheaf of an ambient product of generators. -/
private lemma exists_ambMono (x : Idx F) : ∃ (t : Amb C I) (m : emb F x ⟶ ambSheaf F t), Mono m :=
  match x with
  | .inl g =>
    ⟨.leaf g, 𝟙 (ambSheaf F (Amb.leaf g)), inferInstanceAs (Mono (𝟙 (ambSheaf F (Amb.leaf g))))⟩
  | .inr ⟨t, S⟩ =>
    ⟨t, ⟨Subfunctor.ι (S.sheafify J)⟩,
      (Sheaf.Hom.mono_iff_presheaf_mono J (Type max u v) _).2
        (inferInstanceAs (Mono (Subfunctor.ι (S.sheafify J))))⟩

/-- The site is closed under subsheaves: a subsheaf of an ambient product of generators is, up to
isomorphism, an object of the site. -/
private lemma exists_iso_of_mono {t : Amb C I} {A : Sheaf J (Type max u v)} (m : A ⟶ ambSheaf F t)
    (hm : Mono m) : ∃ W : Site F, Nonempty ((incl F).obj W ≅ A) := by
  have := hm
  refine ⟨Sum.inr ⟨t, Subfunctor.range m.hom⟩, ⟨?_⟩⟩
  have : Mono (Sheaf.toImage m) := mono_of_mono_fac (Sheaf.toImage_ι m)
  have : IsIso (Sheaf.toImage m) := Balanced.isIso_of_mono_of_epi _
  exact (asIso (Sheaf.toImage m)).symm

private lemma hasTerminal_site : HasTerminal (Site F) := by
  obtain ⟨W, ⟨e⟩⟩ := exists_iso_of_mono F (𝟙 (ambSheaf F (Amb.nil : Amb C I))) inferInstance
  exact
    (IsTerminal.isTerminalOfObj (incl F) W ((isTerminalAmbSheafNil F).ofIso e.symm)).hasTerminal

/-- A fibre product is a subobject of the product: the map `X ×_Z Y ⟶ AX ⨯ AY` induced by two
monomorphisms `X ⟶ AX` and `Y ⟶ AY` is a monomorphism. -/
private lemma mono_prod_lift {A : Type*} [Category A] {X Y Z AX AY : A} (f : X ⟶ Z) (g : Y ⟶ Z)
    [HasPullback f g] [HasBinaryProduct AX AY] (mX : X ⟶ AX) (mY : Y ⟶ AY) [Mono mX] [Mono mY] :
    Mono (prod.lift (pullback.fst f g ≫ mX) (pullback.snd f g ≫ mY)) :=
  ⟨fun _ _ h =>
    pullback.hom_ext
      (by
        rw [← cancel_mono mX]; simpa using h =≫ prod.fst)
      (by
        rw [← cancel_mono mY]; simpa using h =≫ prod.snd)⟩

private lemma hasPullback_site {X Y Z : Site F} (f : X ⟶ Z) (g : Y ⟶ Z) : HasPullback f g := by
  obtain ⟨tX, mX, hmX⟩ := exists_ambMono F X
  obtain ⟨tY, mY, hmY⟩ := exists_ambMono F Y
  have := hmX
  have := hmY
  obtain ⟨W, ⟨e⟩⟩ :=
    exists_iso_of_mono F (t := .node tX tY)
      (prod.lift (pullback.fst f.hom g.hom ≫ mX) (pullback.snd f.hom g.hom ≫ mY))
      (mono_prod_lift f.hom g.hom mX mY)
  have hcomm :
    (InducedCategory.homMk (e.hom ≫ pullback.fst f.hom g.hom) : W ⟶ X) ≫ f =
      (InducedCategory.homMk (e.hom ≫ pullback.snd f.hom g.hom) : W ⟶ Y) ≫ g :=
    InducedCategory.hom_ext (by simp [pullback.condition])
  exact
    (IsPullback.of_map (incl F) hcomm
        (IsPullback.of_iso_pullback ⟨by simp [pullback.condition]⟩ e rfl rfl)).hasPullback

private lemma hasFiniteLimits_site : HasFiniteLimits (Site F) := by
  have := hasTerminal_site F
  have : ∀ {X Y Z : Site F} {f : X ⟶ Z} {g : Y ⟶ Z}, HasLimit (cospan f g) := fun {_ _ _} {f g} =>
    hasPullback_site F f g
  have := hasPullbacks_of_hasLimit_cospan (C := Site F)
  exact hasFiniteLimits_of_hasTerminal_and_pullbacks

/-- `G : C ⥤ D` preserves all finite limits that exist in `C`. -/
private lemma preservesFiniteLimits_vv : PreservesFiniteLimits (vv F) := by
  have : PreservesFiniteLimits (vv F ⋙ incl F) :=
    preservesFiniteLimits_of_natIso
      (F := uliftYoneda.{u} ⋙ presheafToSheaf J (Type max u v)) (Iso.refl _)
  exact preservesFiniteLimits_of_reflects_of_preserves (vv F) (incl F)

/-! ### Sections of an object of the site -/

/-- `Θ P` is the presheaf `X ↦ Mor_{Sh(C)}(X, P)` on the site, for `P` a sheaf on `C`. -/
private noncomputable abbrev Theta : Sheaf J (Type max u v) ⥤ ((Site F)ᵒᵖ ⥤ Type max u v) :=
  Stacks.Topos.SiteOfSubcategory.Theta (ι := incl F)

/-- The representable presheaf of an object `V` of the site is `Θ` of the sheaf it is. -/
private noncomputable def yonedaTheta (V : Site F) :
    yoneda.obj V ≅ (Theta F).obj ((incl F).obj V) :=
  NatIso.ofComponents (fun _ => Equiv.toIso InducedCategory.homEquiv)
    (by
      intro X Y m; ext a; rfl)

end Site

/-! ### Sheaves on the site -/

section DenseSubsite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {I : Type max u v}
  (F : I → Sheaf J (Type max u v)) [inst : (vv F).IsDenseSubsite J (top F)]

/-- The inverse image `g⁻¹ : Sh(D) ⥤ Sh(C)` of the morphism of topoi attached to `G`. -/
private noncomputable abbrev gInv : Sheaf (top F) (Type max u v) ⥤ Sheaf J (Type max u v) :=
  (vv F).sheafPushforwardContinuous (Type max u v) J (top F)

/-- The pushforward `g_* : Sh(C) ⥤ Sh(D)` of the morphism of topoi attached to `G`. -/
private noncomputable abbrev gStar : Sheaf J (Type max u v) ⥤ Sheaf (top F) (Type max u v) :=
  (vv F).sheafPushforwardCocontinuous (Type max u v) J (top F)

/-- The adjunction `g⁻¹ ⊣ g_*`. -/
private noncomputable abbrev adjG : gInv F ⊣ gStar F :=
  (vv F).sheafAdjunctionCocontinuous (Type max u v) J (top F)

omit inst in
/-- The functor `G : C ⥤ D` followed by the inclusion is `U ↦ h_U^#`. -/
private noncomputable def vvIncl : vv F ⋙ incl F ≅ Sheaf.sheafifiedYoneda J := Iso.refl _

/-- `bigEquiv` as a natural isomorphism in both variables. -/
private noncomputable def natA : sheafToPresheaf (top F) (Type max u v) ≅ gInv F ⋙ Theta F :=
  Stacks.Topos.SiteOfSubcategory.natA (vvIncl F)

/-- The counit `g⁻¹g_*ℱ ≅ ℱ`. -/
private noncomputable def counitIso (P : Sheaf J (Type max u v)) :
    (gInv F).obj ((gStar F).obj P) ≅ P :=
  asIso ((adjG F).counit.app P)

/-- The unit `𝒢 ≅ g_*g⁻¹𝒢`. -/
private noncomputable def unitIso (𝒢 : Sheaf (top F) (Type max u v)) :
    𝒢 ≅ (gStar F).obj ((gInv F).obj 𝒢) :=
  Iso.app (asIso (adjG F).unit) 𝒢

/-- The pushforward `g_*P` is the presheaf `X ↦ Mor_{Sh(C)}(X, P)`. -/
private noncomputable def thetaIso (P : Sheaf J (Type max u v)) :
    ((gStar F).obj P).obj ≅ (Theta F).obj P :=
  (natA F).app ((gStar F).obj P) ≪≫ (Theta F).mapIso (counitIso F P)

/-- The presheaf represented by an object `V` of `D` is `g_*V`. -/
private noncomputable def yonedaIsoGStar (V : Site F) :
    yoneda.obj V ≅ ((gStar F).obj ((incl F).obj V)).obj :=
  yonedaTheta F V ≪≫ (thetaIso F ((incl F).obj V)).symm

/-- The topology on `D` is subcanonical. -/
private lemma subcanonical_top : (top F).Subcanonical :=
  GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj _ fun V => by
    rw [← isSheaf_iff_isSheaf_of_type]
    exact
      (Presheaf.isSheaf_of_iso_iff (yonedaIsoGStar F V)).mpr
        ((gStar F).obj ((incl F).obj V)).property

/-- `g_*` of an object of `D` is representable. -/
private lemma isRepresentable_gStar_incl (V : Site F) :
    ((gStar F).obj ((incl F).obj V)).obj.IsRepresentable :=
  Functor.IsRepresentable.mk' (yonedaIsoGStar F V)

/-- Every subsheaf of a representable sheaf on `D` is representable. -/
private lemma isRepresentable_of_mono [(top F).Subcanonical] (V : Site F)
    (𝒢 : Sheaf (top F) (Type max u v)) (i : 𝒢 ⟶ (top F).yoneda.obj V) (hi : Mono i) :
    𝒢.obj.IsRepresentable := by
  have := hi
  have iso1 : (top F).yoneda.obj V ≅ (gStar F).obj ((incl F).obj V) :=
    (fullyFaithfulSheafToPresheaf (top F) (Type max u v)).preimageIso (yonedaIsoGStar F V)
  obtain ⟨t, mV, hmV⟩ := exists_ambMono F V
  have := hmV
  obtain ⟨W, ⟨eW⟩⟩ :=
    exists_iso_of_mono F ((gInv F).map (i ≫ iso1.hom) ≫ (counitIso F ((incl F).obj V)).hom ≫ mV)
      inferInstance
  exact
    Functor.IsRepresentable.mk'
      (yonedaIsoGStar F W ≪≫
        (sheafToPresheaf (top F) (Type max u v)).mapIso
          ((gStar F).mapIso eW ≪≫ (unitIso F 𝒢).symm))

end DenseSubsite

end Stacks.Topos.GoodSitePresentation

namespace CategoryTheory.GrothendieckTopology

@[expose] public section

open Stacks.Topos.GoodSitePresentation in
/-- Let `(C, J)` be a site and let `F : ι → Sheaf J (Type max u v)` be a set of
sheaves of sets on `C`. Then there is a site `(D, K)` and a special cocontinuous functor
`G : C ⥤ D` (Stacks 03CG: a functor exhibiting `(C, J)` as a dense subsite of `(D, K)`), so
that the induced morphism of topoi `g : Sh(C) → Sh(D)` is an equivalence, such that

1. `K` is subcanonical;
3. `D` has all finite limits, i.e. fibre products and a final object;
4. every subsheaf of a representable sheaf on `D` is representable; and
5. each `g_* (F i) = (G.sheafPushforwardCocontinuous _ J K).obj (F i)` is representable;

moreover `G` preserves all finite limits that exist in `C`. -/
@[stacks 03CI "Any topos is equivalent, by a special cocontinuous functor, to the topos of
  sheaves on a site which is subcanonical, has all finite limits, has all subsheaves of
  representables representable, and on which a prescribed set of sheaves becomes representable.
  This is conclusions (1), (3), (4) and (5); conclusion (2) holds for every topology and is
  `ofArrows_mem_iff_isLocallySurjective_sigmaDesc_uliftYoneda_map`. The functor is also recorded
  to preserve all finite limits that exist in the given site.",
  sga "4 IV 1.2" "i) => i')"]
public theorem exists_isDenseSubsite_subcanonical_hasFiniteLimits_representable {C : Type u}
    [Category.{v} C] (J : GrothendieckTopology C) {ι : Type max u v}
    (F : ι → Sheaf J (Type max u v)) :
    ∃ (D : Type max u v) (_ : SmallCategory D) (K : GrothendieckTopology D) (G : C ⥤ D) (_ :
      G.IsDenseSubsite J K) (_ : K.Subcanonical) (_ : HasFiniteLimits D)
      (_ : PreservesFiniteLimits G),
      (∀ (V : D) (ℱ : Sheaf K (Type max u v)) (i : ℱ ⟶ K.yoneda.obj V),
          Mono i → ℱ.obj.IsRepresentable) ∧
        (∀ i,
          ((G.sheafPushforwardCocontinuous (Type max u v) J K).obj
              (F i)).obj.IsRepresentable) := by
  let inst := isDenseSubsite_vv F
  let hsub := subcanonical_top F
  exact ⟨Site F, inferInstance, top F, vv F, inst, hsub, hasFiniteLimits_site F,
    preservesFiniteLimits_vv F, fun V ℱ i hi ↦ isRepresentable_of_mono F V ℱ i hi,
    fun i ↦ isRepresentable_gStar_incl F (Sum.inl (Sum.inr i))⟩

end

end CategoryTheory.GrothendieckTopology

end
