module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import StacksFrontier.Deformation.RingedSpaceThickening.ExistenceObstruction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Boundary maps in the `Ext` sequence, and extensions along a functor

This file is about the boundary map of the covariant long exact `Ext` sequence of a short exact
sequence, and about the behaviour of `Ext¹` under a fully faithful exact functor.

For an exact functor: the induced map on `Ext¹` is injective when the functor is fully faithful,
it is compatible with Yoneda composition with a degree zero class, and it carries the class of a
Yoneda extension to the class of a Yoneda extension whose middle term it realizes. In an abelian
category: the Yoneda product of a degree one class with the class of a short exact sequence
vanishes exactly when the class lifts to the middle term; pushing out and pulling back a short
exact sequence keeps it short exact; a map out of an epimorphic quotient which agrees with a
cokernel is a monomorphism; and an extension whose middle term descends along a fully faithful
exact functor descends.

## Main results

* `CategoryTheory.Functor.extMap_injective_of_fullyFaithful`: a fully faithful exact functor is
  injective on `Ext¹`.
* `CategoryTheory.Functor.mapExtAddHom_comp_mk₀` and
  `CategoryTheory.Functor.mapExtAddHom_extClass_of_yoneda_iso`: the map induced on `Ext¹`
  commutes with Yoneda composition with a degree zero class, and takes the class of a Yoneda
  extension to the class of one with isomorphic middle term.
* `CategoryTheory.Abelian.extensionClass_boundary_eq_zero_iff_lifts`: the boundary of a degree
  one class vanishes exactly when the class comes from the middle term.
* `CategoryTheory.Abelian.boundary_eq_zero_iff_exists_action`: for an action of `Ext¹` by maps
  out of a fixed object whose kernel is the image of `Ext¹` upstairs, the boundary of a class
  vanishes exactly when a prescribed map is in the range of the action.
* `CategoryTheory.Abelian.comp_extClass_naturality`: a map of short exact sequences carries the
  Yoneda product of a degree one class with the class of the source sequence to the Yoneda
  product with the class of the target sequence.
* `CategoryTheory.Abelian.mono_of_cokernel_diagram`: a map out of a quotient agreeing with a
  cokernel map is a monomorphism.
* `CategoryTheory.Abelian.shortExact_pushout` and `CategoryTheory.Abelian.shortExact_pullback`:
  the pushout of a short exact sequence along a map out of its kernel term, as a Yoneda
  extension, and the pullback along a map into its quotient term.
* `CategoryTheory.Abelian.yonedaExtension_descend`: an extension between images of a fully
  faithful exact functor whose middle term is in the essential image is the image of one.

## References

* [Stacks Project, Tag 08MF](https://stacks.math.columbia.edu/tag/08MF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe e eY v u v' u'

namespace CategoryTheory

namespace Functor

variable {𝒜 : Type u} [Category.{v, u} 𝒜] [Abelian 𝒜] [HasExt.{e} 𝒜]
  {ℬ : Type u'} [Category.{v', u'} ℬ] [Abelian ℬ] [HasExt.{eY} ℬ]

/-- **A fully faithful exact functor is injective on `Ext¹`.** -/
lemma extMap_injective_of_fullyFaithful (R : 𝒜 ⥤ ℬ) [R.Additive] [PreservesFiniteLimits R]
    [PreservesFiniteColimits R] [R.Full] [R.Faithful] (F K : 𝒜) :
    Function.Injective (R.mapExtAddHom F K 1) := by
  let e𝒜 := Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum 𝒜 F K
  intro x y hxy
  obtain ⟨E, i, p, w, hS, rfl⟩ := e𝒜.1 x
  obtain ⟨E', i', p', w', hS', rfl⟩ := e𝒜.1 y
  rw [Functor.mapExtAddHom_apply, Functor.mapExtAddHom_apply,
    Abelian.Ext.mapExactFunctor_extClass, Abelian.Ext.mapExactFunctor_extClass] at hxy
  obtain ⟨φ, hφ₁, hφ₂⟩ :=
    ((Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum ℬ (R.obj F) (R.obj K)).2.1
      _ _ _ _ _ _ _ _ (hS.map_of_exact R) (hS'.map_of_exact R)).1 hxy
  exact (e𝒜.2.1 E E' i p w i' p' w' hS hS').2
    ⟨R.preimageIso φ, R.map_injective (by simpa using hφ₁), R.map_injective (by simpa using hφ₂)⟩

/-- **The map induced on `Ext¹` commutes with Yoneda composition with a degree zero class.**
Pushing a class forward along a map and then applying an exact functor is applying the functor
and then pushing forward along the image of the map. -/
lemma mapExtAddHom_comp_mk₀ (R : 𝒜 ⥤ ℬ) [R.Additive] [PreservesFiniteLimits R]
    [PreservesFiniteColimits R] {F K L : 𝒜} (ξ : Abelian.Ext F K 1) (γ : K ⟶ L) :
    R.mapExtAddHom F L 1 (ξ.comp (Abelian.Ext.mk₀ γ) (add_zero 1)) =
      (R.mapExtAddHom F K 1 ξ).comp (Abelian.Ext.mk₀ (R.map γ)) (add_zero 1) := by
  simp only [Functor.mapExtAddHom_apply, Abelian.Ext.mapExactFunctor_comp,
    Abelian.Ext.mapExactFunctor_mk₀]

/-- **The image of the class of a Yoneda extension.** If an exact functor carries the middle
term of a degree one Yoneda extension isomorphically onto the middle term of a second one, over
the end terms, then it carries the class of the first to the class of the second. -/
lemma mapExtAddHom_extClass_of_yoneda_iso (R : 𝒜 ⥤ ℬ) [R.Additive] [PreservesFiniteLimits R]
    [PreservesFiniteColimits R] {F K : 𝒜} (D : Abelian.YonedaExtension F K 0)
    (E : Abelian.YonedaExtension (R.obj F) (R.obj K) 0) (m : R.obj D.Z.left ≅ E.Z.left)
    (hf : R.map D.f ≫ m.hom = E.f) (hg : m.hom ≫ E.g = R.map D.g) :
    R.mapExtAddHom F K 1 (Abelian.YonedaExtension.shortExact D).extClass =
      (Abelian.YonedaExtension.shortExact E).extClass := by
  rw [Functor.mapExtAddHom_apply, Abelian.Ext.mapExactFunctor_extClass]
  exact ((Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum ℬ (R.obj F)
    (R.obj K)).2.1 _ _ _ _ _ _ _ _ ((Abelian.YonedaExtension.shortExact D).map_of_exact R)
      (Abelian.YonedaExtension.shortExact E)).2 ⟨m, hf, hg⟩

end Functor

namespace Abelian

variable {𝒜 : Type u} [Category.{v, u} 𝒜] [Abelian 𝒜]

/-- **The boundary of a degree one class.** For a short exact sequence `0 ⟶ K ⟶ P ⟶ Q ⟶ 0`, the
Yoneda product of `ξ : Ext¹(F, Q)` with its class vanishes exactly when `ξ` is pushed forward
from a class in `Ext¹(F, P)`. -/
lemma extensionClass_boundary_eq_zero_iff_lifts [HasExt.{e} 𝒜] {F K P Q : 𝒜} {j : K ⟶ P}
    {q : P ⟶ Q} {hj : j ≫ q = 0} (hS : (ShortComplex.mk j q hj).ShortExact)
    (ξ : Abelian.Ext F Q 1) :
    (ξ.comp hS.extClass (by decide) : Abelian.Ext F K 2) = 0 ↔
      ∃ η : Abelian.Ext F P 1, η.comp (Abelian.Ext.mk₀ q) (add_zero 1) = ξ := by
  refine ⟨fun h => Abelian.Ext.covariant_sequence_exact₃ F hS ξ (by decide) h, ?_⟩
  rintro ⟨η, rfl⟩
  rw [Abelian.Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass]
  simp

/-- **A map of short exact sequences carries one Yoneda product to another.** Let `φ` be a map
from `S₂` to `S₁`, and let `ξ₂ : Ext¹(F, S₂.X₃)` push forward along `φ.τ₃` to
`ξ₁ : Ext¹(F, S₁.X₃)`. Then the Yoneda product of `ξ₁` with the class of `S₁` is the Yoneda
product of `ξ₂` with the class of `S₂`, pushed forward along `φ.τ₁`. -/
lemma comp_extClass_naturality [HasExt.{e} 𝒜] {S₁ S₂ : ShortComplex 𝒜} (h₁ : S₁.ShortExact)
    (h₂ : S₂.ShortExact) (φ : S₂ ⟶ S₁) {F : 𝒜} (ξ₁ : Abelian.Ext F S₁.X₃ 1)
    (ξ₂ : Abelian.Ext F S₂.X₃ 1)
    (hξ : ξ₁ = ξ₂.comp (Abelian.Ext.mk₀ φ.τ₃) (add_zero 1)) :
    ξ₁.comp h₁.extClass (show 1 + 1 = 2 from rfl) =
      (ξ₂.comp h₂.extClass (show 1 + 1 = 2 from rfl)).comp
        (Abelian.Ext.mk₀ φ.τ₁) (add_zero 2) := by
  rw [hξ, Abelian.Ext.comp_assoc_of_second_deg_zero,
    ← ShortComplex.ShortExact.extClass_naturality h₂ h₁ φ,
    Abelian.Ext.comp_assoc_of_third_deg_zero]

/-- **A map agreeing with a cokernel is a monomorphism.** If `q` exhibits its target as the
cokernel of `f ≫ l` for a monomorphism `l`, and `d` is a map out of an epimorphic quotient `b`
of the source of `l` killing `f` with `b ≫ d = l ≫ q`, then `d` is a monomorphism. -/
lemma mono_of_cokernel_diagram {A B C D E : 𝒜} (f : A ⟶ B) (l : B ⟶ C) [Mono l] (q : C ⟶ D)
    (w : f ≫ l ≫ q = 0)
    (hq : IsColimit (CokernelCofork.ofπ (f := f ≫ l) q
      (by simpa only [Category.assoc] using w)))
    (b : B ⟶ E) [Epi b] (hb : f ≫ b = 0) (d : E ⟶ D) (hd : b ≫ d = l ≫ q) : Mono d := by
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  let T := ShortComplex.mk (f ≫ l) q (by simpa only [Category.assoc] using w)
  let k := cokernel.desc f (l ≫ q) w
  let φ : S ⟶ T :=
    { τ₁ := 𝟙 A
      τ₂ := l
      τ₃ := k
      comm₁₂ := by simp [S, T]
      comm₂₃ := by simp [S, T, k] }
  have hT : T.Exact := ShortComplex.exact_of_g_is_cokernel T hq
  have : Mono k := ShortComplex.mono_of_epi_of_epi_of_mono φ hT
    (by dsimp [S]; infer_instance) (by dsimp [φ]; infer_instance)
    (by dsimp [φ]; infer_instance)
  let b' := cokernel.desc f b hb
  have hb' : cokernel.π f ≫ b' = b := cokernel.π_desc _ _ _
  have hk : b' ≫ d = k := by
    apply (cancel_epi (cokernel.π f)).1
    simpa only [Category.assoc, b', k, cokernel.π_desc_assoc, cokernel.π_desc] using hd
  have : Epi b' := epi_of_epi_fac hb'
  have : Mono b' := mono_of_mono_fac hk
  have : IsIso b' := isIso_of_mono_of_epi b'
  have he : inv b' ≫ k = d := by rw [← hk, IsIso.inv_hom_id_assoc]
  rw [← he]
  infer_instance

/-- **The pushout of a short exact sequence, as a Yoneda extension.** Pushing a short exact
sequence out along a map `γ` out of its kernel term gives a degree one Yoneda extension of the
same quotient term by the target of `γ`, receiving the middle term of the original. -/
@[sga "3 III 4.1" "partial"]
lemma shortExact_pushout {S : ShortComplex 𝒜} (hS : S.ShortExact) {K : 𝒜} (γ : S.X₁ ⟶ K) :
    ∃ (E : Abelian.YonedaExtension S.X₃ K 0) (u : S.X₂ ⟶ E.Z.left),
      S.f ≫ u = γ ≫ E.f ∧ u ≫ E.g = S.g :=
  ⟨Abelian.shortExactYonedaExtension (pushoutShortComplex_shortExact hS γ), pushout.inl S.f γ,
    f_comp_pushout_inl S γ, inl_pushoutShortComplex_g S γ⟩

/-- **Base change of a short exact sequence.** Pulling a short exact sequence back along a map
`φ` into its quotient term gives a short exact sequence with the same kernel term and with the
source of `φ` as quotient term. -/
lemma shortExact_pullback {S : ShortComplex 𝒜} (hS : S.ShortExact) {M : 𝒜} (φ : M ⟶ S.X₃) :
    (ShortComplex.mk (pullback.lift 0 S.f (by simp)) (pullback.fst φ S.g)
      (pullback.lift_fst _ _ _)).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  have hm : Mono (pullback.lift (0 : S.X₁ ⟶ M) S.f (by simp) : _ ⟶ pullback φ S.g) :=
    mono_of_mono_fac (pullback.lift_snd _ _ _)
  refine { exact := ?_, mono_f := hm, epi_g := inferInstance }
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A a ha
  have hzero : (a ≫ pullback.snd φ S.g) ≫ S.g = 0 := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, ha, zero_comp]
  refine ⟨A, 𝟙 A, inferInstance, hS.exact.lift _ hzero, ?_⟩
  apply pullback.hom_ext
  · simpa only [Category.id_comp, Category.assoc, pullback.lift_fst, comp_zero] using ha
  · simp only [Category.id_comp, Category.assoc, pullback.lift_snd]
    exact (hS.exact.lift_f _ hzero).symm

/-- **Descent of an extension.** An extension of `R.obj F` by `R.obj K` for a fully faithful
exact functor `R` whose middle term lies in the essential image of `R` is, up to an isomorphism
of middle terms, the image under `R` of an extension of `F` by `K`. -/
lemma yonedaExtension_descend {ℬ : Type u'} [Category.{v', u'} ℬ] [Abelian ℬ] (R : 𝒜 ⥤ ℬ)
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (hR : R.FullyFaithful) {F K : 𝒜}
    (E : Abelian.YonedaExtension (R.obj F) (R.obj K) 0) (hE : R.essImage E.Z.left) :
    ∃ (D : Abelian.YonedaExtension F K 0) (e : R.obj D.Z.left ≅ E.Z.left),
      R.map D.f ≫ e.hom = E.f ∧ e.hom ≫ E.g = R.map D.g := by
  have := hR.full
  have := hR.faithful
  exact exists_yonedaExtension_descent R E hE

/-- **The boundary vanishes exactly when a prescribed map is realized.** Let `a` be a natural
family of maps `Ext¹(R F, R K) ⟶ (T ⟶ K)` whose kernel is the image of `Ext¹(F, K)`. For a short
exact sequence `S`, a class `x` on a map `u` into its middle term and a prescribed `c : T ⟶ S.X₁`
compatible with `x`, the boundary of a class `y` lifting the pushforward of `x` vanishes exactly
when `c` is in the range of `a`. -/
lemma boundary_eq_zero_iff_exists_action [HasExt.{e} 𝒜] {ℬ : Type u'} [Category.{v', u'} ℬ]
    [Abelian ℬ] [HasExt.{eY} ℬ] (R : 𝒜 ⥤ ℬ) [R.Additive] [PreservesFiniteLimits R]
    [PreservesFiniteColimits R] [R.Full] [R.Faithful] (F T : 𝒜)
    (a : ∀ K : 𝒜, Abelian.Ext (R.obj F) (R.obj K) 1 →+ (T ⟶ K))
    (ha : ∀ {K L : 𝒜} (x : Abelian.Ext (R.obj F) (R.obj K) 1) (f : K ⟶ L),
      a L (x.comp (Abelian.Ext.mk₀ (R.map f)) (add_zero 1)) = a K x ≫ f)
    (hker : ∀ (K : 𝒜) (x : Abelian.Ext (R.obj F) (R.obj K) 1),
      a K x = 0 ↔ ∃ y : Abelian.Ext F K 1, R.mapExtAddHom F K 1 y = x)
    {S : ShortComplex 𝒜} (hS : S.ShortExact) {Q : 𝒜} (u : Q ⟶ S.X₂)
    (x : Abelian.Ext (R.obj F) (R.obj Q) 1) (c : T ⟶ S.X₁) (hc : a Q x ≫ u = c ≫ S.f)
    (y : Abelian.Ext F S.X₃ 1)
    (hxy : (x.comp (Abelian.Ext.mk₀ (R.map u)) (add_zero 1)).comp
      (Abelian.Ext.mk₀ (R.map S.g)) (add_zero 1) = R.mapExtAddHom F S.X₃ 1 y) :
    y.comp hS.extClass (show 1 + 1 = 2 from rfl) = 0 ↔
      ∃ z : Abelian.Ext (R.obj F) (R.obj S.X₁) 1, a S.X₁ z = c := by
  have : Mono S.f := hS.mono_f
  let xP := x.comp (Abelian.Ext.mk₀ (R.map u)) (add_zero 1)
  constructor
  · intro h
    obtain ⟨η, hη⟩ := (extensionClass_boundary_eq_zero_iff_lifts hS y).1 h
    let δ := xP - R.mapExtAddHom F S.X₂ 1 η
    have hδ : δ.comp (Abelian.Ext.mk₀ (R.map S.g)) (add_zero 1) = 0 := by
      have hmap := Functor.mapExtAddHom_comp_mk₀ R η S.g
      rw [hη] at hmap
      dsimp only [δ, xP]
      simp only [sub_eq_add_neg, Abelian.Ext.add_comp, Abelian.Ext.neg_comp, ← hmap, hxy,
        add_neg_cancel]
    obtain ⟨z, hz⟩ :=
      Abelian.Ext.covariant_sequence_exact₂ (R.obj F) (hS.map_of_exact R) δ hδ
    refine ⟨z, (cancel_mono S.f).1 ?_⟩
    calc
      a S.X₁ z ≫ S.f = a S.X₂ δ := (ha z S.f).symm.trans (congrArg (a S.X₂) hz)
      _ = c ≫ S.f := by
        show a S.X₂ (xP - R.mapExtAddHom F S.X₂ 1 η) = _
        rw [map_sub, (hker S.X₂ _).2 ⟨η, rfl⟩, sub_zero, ha]
        exact hc
  · rintro ⟨z, hz⟩
    let zP := z.comp (Abelian.Ext.mk₀ (R.map S.f)) (add_zero 1)
    let δ := xP - zP
    have hδ : a S.X₂ δ = 0 := by
      show a S.X₂ (xP - zP) = 0
      rw [map_sub, ha, ha, hz, hc, sub_self]
    obtain ⟨η, hη⟩ := (hker S.X₂ δ).1 hδ
    have hzP : zP.comp (Abelian.Ext.mk₀ (R.map S.g)) (add_zero 1) = 0 := by
      dsimp only [zP]
      rw [Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀, ← R.map_comp,
        S.zero, R.map_zero, Abelian.Ext.mk₀_zero, Abelian.Ext.comp_zero]
    apply (extensionClass_boundary_eq_zero_iff_lifts hS y).2
    refine ⟨η, R.extMap_injective_of_fullyFaithful F S.X₃ ?_⟩
    rw [Functor.mapExtAddHom_comp_mk₀ R η S.g, hη]
    dsimp only [δ, xP]
    simp only [sub_eq_add_neg, Abelian.Ext.add_comp, Abelian.Ext.neg_comp, hxy, hzP, neg_zero,
      add_zero]

end Abelian

end CategoryTheory

end
