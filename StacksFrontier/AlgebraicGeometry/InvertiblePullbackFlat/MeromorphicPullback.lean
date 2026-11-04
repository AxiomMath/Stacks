module

public import Mathlib.Topology.Sheaves.Functors
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.PullbackCriteria
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.TotalQuotient
import StacksCore.Tactic.StacksAttribute

/-!
# Pulling meromorphic functions back along a morphism

Stacks Tag 02OT says what it means for *pullbacks of meromorphic functions to be defined* for a
morphism `f : X ⟶ Y`, and Tag 02OU gives criteria. Both are already formalized, as the predicate
`AlgebraicGeometry.PullbacksMeromorphicSections` and a family of sufficient conditions for it.
What was missing is the object those conditions are conditions *for*: the actual morphism
`𝒦_Y ⟶ f_* 𝒦_X` of sheaves of total quotient rings. Without it, a statement such as the one in
the proof of Tag 0BD7 — "let `𝒩 ⊂ 𝒦_Y` be the module of those `g` with `f^*(g) s ∈ ℒ`" — cannot
even be written down.

This file builds that morphism. A section of `𝒦_Y` over `V` is, before sheafification, a
fraction `a / s` with `s` a section of `𝒪_Y` whose germ at every point of `V` is a
nonzerodivisor. Pulling back the numerator and the denominator along `f` makes sense as soon as
the pulled-back denominator is again a nonzerodivisor germwise, which is exactly what
`PullbacksMeromorphicSections` asserts; so the comparison is obtained from the universal
property of a localization, objectwise, followed by that of sheafification.

The hypothesis cannot be dropped. For the closed immersion `f : Spec k ⟶ Spec k[x]` at the
origin, `𝒦_Y` is the function field `k(x)` and `𝒦_X = k`, and no ring map `k(x) ⟶ k` extends
`k[x] ⟶ k`, because `x` is inverted on the left and sent to `0` on the right.

## Main definitions

* `Stacks.Meromorphic.submonoidPresheafLift`: the universal property of Mathlib's sectionwise
  localization `TopCat.Presheaf.SubmonoidPresheaf.localizationPresheaf` — a morphism of
  presheaves of rings out of the localization, from one out of the original presheaf which
  inverts every prescribed section.
* `Stacks.Meromorphic.totalQuotientPresheafPullback`: the comparison before sheafification.
* `Stacks.Meromorphic.totalQuotientSheafPullback`: the morphism `𝒦_Y ⟶ f_* 𝒦_X`.
* `Stacks.Meromorphic.Scheme.totalQuotientSheafPullbackOfFlat`: the same for a flat morphism of
  schemes, where no hypothesis has to be supplied.

## Main results

* `Stacks.Meromorphic.isRegularSectionOn_iff_germ`: a section of the structure sheaf is regular
  on an open exactly when its germ at every point of that open is a nonzerodivisor. This is the
  form of Tag 01WZ that the denominators of the total quotient presheaf are phrased in.
* `Stacks.Meromorphic.mem_denominators_iff`: consequently, the denominator submonoid of the
  total quotient presheaf over an open consists of the sections that are regular there.
* `Stacks.Meromorphic.isRegularSectionOn_appPullback`: when pullbacks of meromorphic functions
  are defined, the pullback of a regular section is regular on the whole inverse image.
* `Stacks.Meromorphic.toTotalQuotientSheaf_comp_totalQuotientSheafPullback`: the square against
  the localization maps `𝒪 ⟶ 𝒦` commutes; this is what identifies the morphism as "pull a
  function back".

## Implementation notes

The universal property of the sheafified sectionwise localization is already in the library at
Tag 0EMC, as
`AlgebraicGeometry.RingedSite.MultiplicativeSubpresheaf.existsUnique_lift_toLocalizationSheaf`,
for an arbitrary ringed site. It is not used here, for two reasons. It is stated for its own
`MultiplicativeSubpresheaf` structure rather than for Mathlib's `SubmonoidPresheaf`, which is
the one `TopCat.Presheaf.totalQuotientPresheaf` — and hence `totalQuotientSheaf` — is actually
defined from; and it produces the morphism only through the existential, so the sections of the
result could not be computed. `submonoidPresheafLift` below is the same mathematics on the
structure the target is built from, with the morphism in hand. No Stacks tag is attached to it:
0EMC is already carried by the ringed-site version, and a second site for one tag is the
pathology this library is trying to retire, not to extend.

Naturality of the lift is proved by cancelling the epimorphism `𝒪 ⟶ 𝒪[S⁻¹]`, which avoids
unfolding `localizationPresheaf.map` and the transparency wall that unfolding runs into.

## References

* [Stacks Project, Tag 02OT](https://stacks.math.columbia.edu/tag/02OT)
* [Stacks Project, Tag 02OU](https://stacks.math.columbia.edu/tag/02OU)
* [Stacks Project, Tag 01WZ](https://stacks.math.columbia.edu/tag/01WZ)
* [Stacks Project, Tag 02AR](https://stacks.math.columbia.edu/tag/02AR)
* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open scoped nonZeroDivisors

universe u

namespace Stacks.Meromorphic

/-! ### The universal property of the sectionwise localization -/

section Lift

variable {X : TopCat.{u}} {F : X.Presheaf CommRingCat.{u}} (G : F.SubmonoidPresheaf)
  {H : X.Presheaf CommRingCat.{u}} (φ : F ⟶ H)
  (hφ : ∀ (U : (Opens X)ᵒᵖ) (s : G.obj U), IsUnit ((φ.app U).hom s))

/-- The component of `Stacks.Meromorphic.submonoidPresheafLift` over an object: the ring map out
of a localization determined by a ring map inverting the localized submonoid. -/
noncomputable def submonoidPresheafLiftApp (U : (Opens X)ᵒᵖ) :
    G.localizationPresheaf.obj U ⟶ H.obj U :=
  CommRingCat.ofHom (IsLocalization.lift (M := G.obj U) (g := (φ.app U).hom) (hφ U))

/-- Each component of the lift extends the corresponding component of the given morphism. -/
lemma toLocalizationPresheaf_app_comp_submonoidPresheafLiftApp (U : (Opens X)ᵒᵖ) :
    G.toLocalizationPresheaf.app U ≫ submonoidPresheafLiftApp G φ hφ U = φ.app U := by
  ext x
  exact IsLocalization.lift_eq (M := G.obj U) (S := Localization (G.obj U)) (hφ U) x

/-- A morphism of presheaves of rings which inverts every section of a submonoid presheaf
factors through the sectionwise localization. -/
noncomputable def submonoidPresheafLift : G.localizationPresheaf ⟶ H where
  app U := submonoidPresheafLiftApp G φ hφ U
  naturality U V i := by
    have : Epi (G.toLocalizationPresheaf.app U) := Localization.epi' (G.obj U)
    rw [← cancel_epi (G.toLocalizationPresheaf.app U), ← Category.assoc,
      ← G.toLocalizationPresheaf.naturality i, Category.assoc,
      toLocalizationPresheaf_app_comp_submonoidPresheafLiftApp, ← Category.assoc,
      toLocalizationPresheaf_app_comp_submonoidPresheafLiftApp, φ.naturality i]

/-- The component of `submonoidPresheafLift` over an object is `submonoidPresheafLiftApp`. -/
@[simp]
lemma submonoidPresheafLift_app (U : (Opens X)ᵒᵖ) :
    (submonoidPresheafLift G φ hφ).app U = submonoidPresheafLiftApp G φ hφ U := rfl

/-- The lift extends the given morphism. -/
lemma toLocalizationPresheaf_comp_submonoidPresheafLift :
    G.toLocalizationPresheaf ≫ submonoidPresheafLift G φ hφ = φ :=
  NatTrans.ext (funext fun U =>
    toLocalizationPresheaf_app_comp_submonoidPresheafLiftApp G φ hφ U)

end Lift

/-! ### Regular sections on an open, read off the stalks -/

namespace Aux

variable {X : TopCat.{u}}

/-- Restricting twice is restricting once. -/
private lemma res_res (F : TopCat.Presheaf CommRingCat.{u} X) {A B C : Opens X}
    (hAB : A ≤ B) (hBC : B ≤ C) (u : F.obj (op C)) :
    F.map (homOfLE hAB).op (F.map (homOfLE hBC).op u) =
      F.map (homOfLE (hAB.trans hBC)).op u := by
  rw [← F.map_comp_apply]
  congr 1

/-- In a commutative ring, multiplication by an element is injective exactly when the element is
a nonzerodivisor. -/
lemma isSMulRegular_iff_mem_nonZeroDivisors (R : CommRingCat.{u}) (a : R) :
    IsSMulRegular R a ↔ a ∈ (R : Type u)⁰ := by
  exact (Commute.isRegular_iff (Commute.all a)).symm.trans isRegular_iff_mem_nonZeroDivisors

/-- For a sheaf of rings, a section of an open restricts to a nonzerodivisor on every smaller
open exactly when its germ at every point of that open is a nonzerodivisor. -/
@[ega "IV 20.1.3" "partial"]
lemma forall_le_iff_germ (F : TopCat.Sheaf CommRingCat.{u} X) (U : Opens X)
    (s : F.presheaf.obj (op U)) :
    (∀ (W : Opens X) (h : W ≤ U),
        IsSMulRegular (F.presheaf.obj (op W)) (F.presheaf.map (homOfLE h).op s)) ↔
      ∀ (x : X) (hx : x ∈ U), IsSMulRegular (F.presheaf.stalk x) (F.presheaf.germ U x hx s) := by
  constructor
  · intro h x hx
    apply IsSMulRegular.of_right_eq_zero_of_smul
    intro a ha
    obtain ⟨W, hxW, t, rfl⟩ := F.presheaf.exists_germ_eq a
    have hmem : x ∈ U ⊓ W := ⟨hx, hxW⟩
    set sU := F.presheaf.map (homOfLE (inf_le_left : U ⊓ W ≤ U)).op s with hsU
    set tW := F.presheaf.map (homOfLE (inf_le_right : U ⊓ W ≤ W)).op t with htW
    have he : F.presheaf.germ (U ⊓ W) x hmem (sU * tW) =
        F.presheaf.germ (U ⊓ W) x hmem 0 := by
      rw [map_mul, map_zero, hsU, htW, F.presheaf.germ_res_apply, F.presheaf.germ_res_apply]
      simpa only [smul_eq_mul] using ha
    obtain ⟨W', hxW', i, j, hij⟩ := F.presheaf.germ_eq x hmem hmem (sU * tW) 0 he
    have hiW : W' ≤ U ⊓ W := i.le
    have hz : F.presheaf.map (homOfLE (hiW.trans inf_le_right)).op t = 0 := by
      refine (h W' (hiW.trans inf_le_left)).right_eq_zero_of_smul ?_
      rw [smul_eq_mul]
      have hi : i = homOfLE hiW := Subsingleton.elim _ _
      rwa [map_zero, hi, map_mul, hsU, htW, res_res, res_res] at hij
    rw [← F.presheaf.germ_res_apply (homOfLE (hiW.trans inf_le_right)) x hxW' t, hz, map_zero]
  · intro h W hW
    apply IsSMulRegular.of_right_eq_zero_of_smul
    intro t ht
    apply TopCat.Presheaf.section_ext F W t 0
    intro x hx
    rw [map_zero]
    refine (h x (hW hx)).right_eq_zero_of_smul ?_
    rw [smul_eq_mul, ← F.presheaf.germ_res_apply (homOfLE hW) x hx s, ← map_mul,
      show F.presheaf.map (homOfLE hW).op s * t = 0 from by simpa only [smul_eq_mul] using ht,
      map_zero]

/-- Regularity of a restricted section transports along an equality of opens. -/
private lemma transport (F : TopCat.Presheaf CommRingCat.{u} X)
    {U W W' : Opens X} (e : W' = W) (h : W ≤ U) (h' : W' ≤ U) (s : F.obj (op U))
    (hr : IsSMulRegular (F.obj (op W')) (F.map (homOfLE h').op s)) :
    IsSMulRegular (F.obj (op W)) (F.map (homOfLE h).op s) := by
  subst e; exact hr

end Aux

/-- A section of the structure sheaf is regular on an open exactly when each of its restrictions
to a smaller open is a nonzerodivisor there. -/
theorem isRegularSectionOn_iff_forall_le (X : LocallyRingedSpace.{u}) (U : Opens X)
    (s : X.presheaf.obj (op U)) :
    IsRegularSectionOn X U s ↔ ∀ (W : Opens X) (h : W ≤ U),
      IsSMulRegular (X.presheaf.obj (op W)) (X.presheaf.map (homOfLE h).op s) := by
  refine Iff.trans (isRegularSection_iff_forall_isSMulRegular
    (X.restrict U.isOpenEmbedding).toSheafedSpace _) ?_
  constructor
  · intro h W hW
    refine Aux.transport X.presheaf (W' := U.isOpenEmbedding.functor.obj
      ((Opens.map U.inclusion').obj W)) ?_ hW ?_ s ?_
    · rw [Opens.functor_map_eq_inf]; exact inf_eq_left.mpr hW
    · rw [Opens.functor_map_eq_inf]; exact inf_le_right
    · exact h ((Opens.map U.inclusion').obj W)
  · intro h W
    exact h (U.isOpenEmbedding.functor.obj W) (by rintro _ ⟨y, _, rfl⟩; exact y.2)

/-- **Stacks Project, Tag 01WZ, over an open.** A section of the structure sheaf is regular on an
open exactly when its germ at every point of that open is a nonzerodivisor. -/
@[ega "IV 20.1.3" "partial"]
theorem isRegularSectionOn_iff_germ (X : LocallyRingedSpace.{u}) (U : Opens X)
    (s : X.presheaf.obj (op U)) :
    IsRegularSectionOn X U s ↔ ∀ (x : X) (hx : x ∈ U),
      IsSMulRegular (X.presheaf.stalk x) (X.presheaf.germ U x hx s) :=
  (isRegularSectionOn_iff_forall_le X U s).trans (Aux.forall_le_iff_germ X.sheaf U s)

/-- The denominators of the total quotient presheaf over an open are exactly the sections that
are regular there. -/
theorem mem_denominators_iff (X : LocallyRingedSpace.{u}) (U : Opens X)
    (s : X.presheaf.obj (op U)) :
    s ∈ (X.presheaf.submonoidPresheafOfStalk fun x => (X.presheaf.stalk x)⁰).obj (op U) ↔
      IsRegularSectionOn X U s := by
  rw [isRegularSectionOn_iff_germ]
  simp only [TopCat.Presheaf.submonoidPresheafOfStalk_obj, Submonoid.mem_iInf,
    Submonoid.mem_comap]
  exact ⟨fun h x hx => (Aux.isSMulRegular_iff_mem_nonZeroDivisors _ _).mpr (h ⟨x, hx⟩),
    fun h x => (Aux.isSMulRegular_iff_mem_nonZeroDivisors _ _).mp (h x.1 x.2)⟩

variable {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)

/-- When pullbacks of meromorphic functions are defined for `f`, the pullback of a section
regular on `V` is regular on the whole of `f ⁻¹ V`. -/
theorem isRegularSectionOn_appPullback (hf : PullbacksMeromorphicSections f)
    (V : Opens Y) (s : Y.presheaf.obj (op V)) (hs : IsRegularSectionOn Y V s) :
    IsRegularSectionOn X ((Opens.map f.base).obj V) (f.c.app (op V) s) := by
  have h := hf ((Opens.map f.base).obj V) V le_rfl s hs
  rw [isRegularSectionOn_iff_germ] at h ⊢
  intro x hx
  have hx' := h x hx
  rwa [X.presheaf.germ_res_apply
    (homOfLE (le_refl ((Opens.map f.base).obj V))) x hx] at hx'

/-! ### The pullback morphism on sheaves of meromorphic functions -/

/-- The pullback comparison on presheaves of total quotient rings: a fraction `a / s` over `V`
goes to `f^*(a) / f^*(s)` over `f ⁻¹ V`, which makes sense because `f^*(s)` is again a
denominator. -/
noncomputable def totalQuotientPresheafPullback (hf : PullbacksMeromorphicSections f) :
    Y.presheaf.totalQuotientPresheaf ⟶
      (TopCat.Presheaf.pushforward CommRingCat.{u} f.base).obj
        (AlgebraicGeometry.totalQuotientSheaf X.sheaf).presheaf :=
  submonoidPresheafLift _
    (f.c ≫ (TopCat.Presheaf.pushforward CommRingCat.{u} f.base).map
      (AlgebraicGeometry.toTotalQuotientSheaf X.sheaf).hom)
    (by
      rintro ⟨V⟩ t
      have hmem : f.c.app (op V) (t : Y.presheaf.obj (op V)) ∈
          (X.presheaf.submonoidPresheafOfStalk fun x => (X.presheaf.stalk x)⁰).obj
            (op ((Opens.map f.base).obj V)) :=
        (mem_denominators_iff X _ _).mpr
          (isRegularSectionOn_appPullback f hf V _ ((mem_denominators_iff Y V _).mp t.2))
      have hu : IsUnit ((X.presheaf.toTotalQuotientPresheaf.app
          (op ((Opens.map f.base).obj V))).hom
            (f.c.app (op V) (t : Y.presheaf.obj (op V)))) :=
        IsLocalization.map_units
          (M := (X.presheaf.submonoidPresheafOfStalk fun x => (X.presheaf.stalk x)⁰).obj
            (op ((Opens.map f.base).obj V)))
          (Localization _) ⟨_, hmem⟩
      have happ : ((f.c ≫ (TopCat.Presheaf.pushforward CommRingCat.{u} f.base).map
          (AlgebraicGeometry.toTotalQuotientSheaf X.sheaf).hom).app (op V)) =
          f.c.app (op V) ≫ (AlgebraicGeometry.toTotalQuotientSheaf X.sheaf).hom.app
            (op ((Opens.map f.base).obj V)) := rfl
      rw [happ, AlgebraicGeometry.toTotalQuotientSheaf_hom]
      exact hu.map ((toSheafify _ X.presheaf.totalQuotientPresheaf).app
        (op ((Opens.map f.base).obj V))).hom)

/-- **The pullback morphism on sheaves of meromorphic functions**, `𝒦_Y ⟶ f_* 𝒦_X`, available
whenever pullbacks of meromorphic functions are defined for `f` (Stacks Tag 02OT). -/
noncomputable def totalQuotientSheafPullback (hf : PullbacksMeromorphicSections f) :
    AlgebraicGeometry.totalQuotientSheaf Y.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj
        (AlgebraicGeometry.totalQuotientSheaf X.sheaf) :=
  (fullyFaithfulSheafToPresheaf _ CommRingCat.{u}).homEquiv.symm
    (sheafifyLift _
      (totalQuotientPresheafPullback f hf)
      ((TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj
        (AlgebraicGeometry.totalQuotientSheaf X.sheaf)).property)

/-- The underlying morphism of presheaves of the pullback morphism. -/
lemma totalQuotientSheafPullback_hom (hf : PullbacksMeromorphicSections f) :
    (totalQuotientSheafPullback f hf).hom =
      sheafifyLift _
        (totalQuotientPresheafPullback f hf)
        ((TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj
          (AlgebraicGeometry.totalQuotientSheaf X.sheaf)).property := rfl

/-- The pullback morphism on meromorphic functions restricts to the pullback of regular
functions: the square against the localization maps `𝒪 ⟶ 𝒦` commutes. -/
lemma toTotalQuotientSheaf_comp_totalQuotientSheafPullback
    (hf : PullbacksMeromorphicSections f) :
    (AlgebraicGeometry.toTotalQuotientSheaf Y.sheaf).hom ≫
        (totalQuotientSheafPullback f hf).hom =
      f.c ≫ (TopCat.Presheaf.pushforward CommRingCat.{u} f.base).map
        (AlgebraicGeometry.toTotalQuotientSheaf X.sheaf).hom := by
  have e1 : (AlgebraicGeometry.toTotalQuotientSheaf Y.sheaf).hom ≫
        (totalQuotientSheafPullback f hf).hom =
      Y.presheaf.toTotalQuotientPresheaf ≫ (toSheafify _ Y.presheaf.totalQuotientPresheaf ≫
        sheafifyLift _ (totalQuotientPresheafPullback f hf)
          ((TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj
            (AlgebraicGeometry.totalQuotientSheaf X.sheaf)).property) := by
    rw [AlgebraicGeometry.toTotalQuotientSheaf_hom, totalQuotientSheafPullback_hom]
    exact Category.assoc _ _ _
  refine e1.trans ((congrArg (fun g => Y.presheaf.toTotalQuotientPresheaf ≫ g)
    (toSheafify_sheafifyLift _ (totalQuotientPresheafPullback f hf) _)).trans ?_)
  exact toLocalizationPresheaf_comp_submonoidPresheafLift _ _ _

/-- `f^*(g)`: a meromorphic function on `V ⊆ Y` pulled back to `f ⁻¹ V ⊆ X`. This is the
operation the submodule `𝒩 ⊂ 𝒦_Y` of Stacks Tag 0BD7 is defined by. -/
noncomputable abbrev pullbackMeromorphic (hf : PullbacksMeromorphicSections f) (V : Opens Y)
    (g : (AlgebraicGeometry.totalQuotientSheaf Y.sheaf).presheaf.obj (op V)) :
    (AlgebraicGeometry.totalQuotientSheaf X.sheaf).presheaf.obj
      (op ((Opens.map f.base).obj V)) :=
  ((totalQuotientSheafPullback f hf).hom.app (op V)).hom g

/-- Pulling back a regular function and then viewing it as a meromorphic function agrees with
viewing it as a meromorphic function and then pulling back. -/
lemma pullbackMeromorphic_toTotalQuotientSheaf (hf : PullbacksMeromorphicSections f)
    (V : Opens Y) (a : Y.presheaf.obj (op V)) :
    pullbackMeromorphic f hf V
        (((AlgebraicGeometry.toTotalQuotientSheaf Y.sheaf).hom.app (op V)).hom a) =
      ((AlgebraicGeometry.toTotalQuotientSheaf X.sheaf).hom.app
        (op ((Opens.map f.base).obj V))).hom (f.c.app (op V) a) :=
  congrArg (fun k => k.hom a)
    (congrArg (fun η => η.app (op V))
      (toTotalQuotientSheaf_comp_totalQuotientSheafPullback f hf))

/-- **The pullback morphism on sheaves of meromorphic functions for a flat morphism of
schemes**, `𝒦_Y ⟶ φ_* 𝒦_X`. Flatness supplies the hypothesis of Stacks Tag 02OT by Tag 02OU, so
no hypothesis has to be carried. This is the input to the scheme-level half of Tag 0BD7. -/
noncomputable def Scheme.totalQuotientSheafPullbackOfFlat
    {X Y : Scheme.{u}} (φ : X ⟶ Y) [Flat φ] :
    Y.totalQuotientSheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} φ.base).obj X.totalQuotientSheaf :=
  totalQuotientSheafPullback φ.toLRSHom (pullbacksMeromorphicSections_of_flat φ)

end Stacks.Meromorphic
