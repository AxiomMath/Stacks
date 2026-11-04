module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksFrontier.CategoryTheory.Sites.Stack.IsomPresheaf

/-!
# Equalizers in a category fibred in groupoids

Let `p : 𝒳 ⥤ 𝒞` be a category fibred in groupoids over a category with equalizers. Two morphisms
`a b : x ⟶ y` of `𝒳` have an equalizer as soon as, for every object `x'` and every automorphism
`i` of `x'` in its fibre, the locus of the base over which `i` restricts to the identity is
represented by a subobject of `p x'`. That locus is the locus on which the two sections `id` and
`i` of the presheaf `Mor(x', x')` of Stacks 02ZB agree, so it is representable whenever two
sections of `Mor(x', x')` always agree on a representable locus — which is what a presheaf with
relatively representable diagonal provides.

This is the argument of Stacks 06WY (2): first replace `x` by its restriction to the equalizer
of `p a` and `p b` in the base, then `b` by `i ≫ a` for the automorphism `i` of the fibre, and
finally `x` by its restriction to the locus where `i` is the identity.

## Main definitions

* `CategoryTheory.Presheaf.HasRepresentableEqualizerLoci`: for any two sections of a presheaf
  over an object `X`, the morphisms `Y ⟶ X` along which they agree are those factoring through a
  fixed monomorphism `M ⟶ X`.

## Main results

* `CategoryTheory.Presheaf.hasRepresentableEqualizerLoci_of_relativelyRepresentable_diag`: a
  presheaf whose diagonal is relatively representable has representable equalizer loci.
* `CategoryTheory.Presheaf.HasRepresentableEqualizerLoci.of_iso` and
  `CategoryTheory.Presheaf.HasRepresentableEqualizerLoci.comp_equivalence`: the property is
  invariant under isomorphisms (after universe lifts) and under precomposition with an
  equivalence.
* `CategoryTheory.Functor.IsFiberedInGroupoids.hasEqualizers_of_morPresheaf`: a category fibred
  in groupoids over a category with equalizers has equalizers if all presheaves `Mor(x, x)` have
  representable equalizer loci.

## References

* [Stacks Project, Tag 06WY](https://stacks.math.columbia.edu/tag/06WY)
* [Stacks Project, Tag 02ZB](https://stacks.math.columbia.edu/tag/02ZB)
-/

@[expose] public section

namespace CategoryTheory

open Limits Opposite

-- `Fiber` must unfold for the endpoints of the restriction maps of `Mor(x, x)` to be seen as
-- equal at `implicit` transparency, as in `StacksFrontier.CategoryTheory.Sites.Stack.IsomPresheaf`.
attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion

universe w w' v₁ v₂ v₃ u₁ u₂ u₃

namespace Presheaf

variable {C : Type u₁} [Category.{v₁} C]

/-- A presheaf `P` has *representable equalizer loci* if for every two sections `s t` of `P`
over an object `X` there is a monomorphism `m : M ⟶ X` such that a morphism `h : Y ⟶ X` factors
through `m` exactly when `s` and `t` agree after restriction along `h`. -/
def HasRepresentableEqualizerLoci (P : Cᵒᵖ ⥤ Type w) : Prop :=
  ∀ ⦃X : C⦄ (s t : P.obj (op X)), ∃ (M : C) (m : M ⟶ X), Mono m ∧
    ∀ ⦃Y : C⦄ (h : Y ⟶ X), P.map h.op s = P.map h.op t ↔ ∃ k : Y ⟶ M, k ≫ m = h

/-- A presheaf whose diagonal is relatively representable has representable equalizer loci:
the locus where two sections `s t` over `X` agree is the pullback of the diagonal along the
morphism `X ⟶ P × P` they define. -/
theorem hasRepresentableEqualizerLoci_of_relativelyRepresentable_diag (P : Cᵒᵖ ⥤ Type v₁)
    (hP : yoneda.relativelyRepresentable (diag P)) : HasRepresentableEqualizerLoci P := by
  intro X s t
  obtain ⟨M, m, fst, hpb⟩ := hP (prod.lift (yonedaEquiv.symm s) (yonedaEquiv.symm t))
  refine ⟨M, m, yoneda.mono_of_mono_map hpb.mono_snd_of_mono, fun Y h => ?_⟩
  rw [← yonedaEquiv.symm.injective.eq_iff, ← yonedaEquiv_symm_naturality_left,
    ← yonedaEquiv_symm_naturality_left]
  constructor
  · intro hst
    have hw : (yoneda.map h ≫ yonedaEquiv.symm s) ≫ diag P =
        yoneda.map h ≫ prod.lift (yonedaEquiv.symm s) (yonedaEquiv.symm t) := by
      ext1 <;> simp [hst]
    refine ⟨Yoneda.fullyFaithful.preimage (hpb.lift _ _ hw), ?_⟩
    apply Yoneda.fullyFaithful.map_injective
    simp
  · rintro ⟨k, rfl⟩
    have h1 := congrArg (fun φ => yoneda.map k ≫ φ ≫ prod.fst) hpb.w
    have h2 := congrArg (fun φ => yoneda.map k ≫ φ ≫ prod.snd) hpb.w
    simp only [Category.assoc, prod.lift_fst, prod.lift_snd, Category.comp_id, diag] at h1 h2
    rw [Functor.map_comp, Category.assoc, ← h1, h2, Category.assoc]

namespace HasRepresentableEqualizerLoci

/-- Representability of equalizer loci transfers along an isomorphism of presheaves, taken after
lifting both to a common universe. -/
theorem of_iso {P : Cᵒᵖ ⥤ Type w} {P' : Cᵒᵖ ⥤ Type w'}
    (e : P ⋙ uliftFunctor.{w'} ≅ P' ⋙ uliftFunctor.{w}) (h : HasRepresentableEqualizerLoci P') :
    HasRepresentableEqualizerLoci P := by
  let φ : ∀ X : Cᵒᵖ, P.obj X → P'.obj X := fun X z =>
    ULift.down ((e.app X).toEquiv (ULift.up z : (P ⋙ uliftFunctor.{w'}).obj X))
  have hφ : ∀ {X Y : Cᵒᵖ} (g : X ⟶ Y) (z : P.obj X), φ Y (P.map g z) = P'.map g (φ X z) :=
    fun {X Y} g z => congrArg ULift.down
      (NatTrans.naturality_apply e.hom g (ULift.up z : (P ⋙ uliftFunctor.{w'}).obj X))
  have inj : ∀ X : Cᵒᵖ, Function.Injective (φ X) := fun X =>
    ULift.down_injective.comp ((e.app X).toEquiv.injective.comp ULift.up_injective)
  intro X s t
  obtain ⟨M, m, hm, H⟩ := h (φ _ s) (φ _ t)
  refine ⟨M, m, hm, fun Y g => ?_⟩
  rw [← H g, ← hφ, ← hφ, (inj _).eq_iff]

/-- Representability of equalizer loci transfers along an isomorphism of presheaves in the same
universe. -/
theorem of_iso' {P P' : Cᵒᵖ ⥤ Type w} (e : P ≅ P') (h : HasRepresentableEqualizerLoci P') :
    HasRepresentableEqualizerLoci P :=
  of_iso.{w, w} (Functor.isoWhiskerRight e uliftFunctor) h

/-- Representability of equalizer loci is preserved by precomposition with an equivalence. -/
theorem comp_equivalence {D : Type u₂} [Category.{v₂} D] (e : C ≌ D) {P : Dᵒᵖ ⥤ Type w}
    (h : HasRepresentableEqualizerLoci P) : HasRepresentableEqualizerLoci (e.functor.op ⋙ P) := by
  intro X s t
  obtain ⟨M, m, hm, H⟩ := h s t
  refine ⟨e.inverse.obj M, e.inverse.map m ≫ e.unitInv.app X, mono_comp _ _, fun Y g => ?_⟩
  show P.map (e.functor.map g).op s = P.map (e.functor.map g).op t ↔ _
  rw [H]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨e.unit.app Y ≫ e.inverse.map k, ?_⟩
    simp [← Functor.map_comp_assoc, hk]
  · rintro ⟨k, hk⟩
    refine ⟨e.functor.map k ≫ e.counit.app M, ?_⟩
    rw [← hk]
    simp

end HasRepresentableEqualizerLoci

end Presheaf

namespace Functor.IsFiberedInGroupoids

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
variable {p : 𝒳 ⥤ 𝒞} (hp : p.IsFiberedInGroupoids)

include hp

/-- A morphism `m : U ⟶ p y` lifts to a morphism `c : z ⟶ y` with `p c = m` up to `eqToHom`. -/
private theorem exists_lift_map_eq_eqToHom_comp {y : 𝒳} {U : 𝒞} (m : U ⟶ p.obj y) :
    ∃ (z : 𝒳) (c : z ⟶ y) (hz : p.obj z = U), p.map c = eqToHom hz ≫ m := by
  obtain ⟨z, c, hc⟩ := hp.exists_lift m y rfl
  exact ⟨z, c, IsHomLift.domain_eq p m c, by simpa using IsHomLift.fac' p m c⟩

/-- Two morphisms `a b : x ⟶ y` of a category fibred in groupoids have an equalizer as soon as
the morphisms `t` into `x` with `t ≫ a = t ≫ b` are exactly those whose image in the base
factors through a fixed monomorphism `m : M ⟶ p x`: the equalizer is a lift of `m` to `x`. -/
theorem hasLimit_parallelPair_of_locus {x y : 𝒳} (a b : x ⟶ y) {M : 𝒞} (m : M ⟶ p.obj x)
    [Mono m] (H : ∀ ⦃w : 𝒳⦄ (t : w ⟶ x), t ≫ a = t ≫ b ↔ ∃ k, k ≫ m = p.map t) :
    HasLimit (parallelPair a b) := by
  obtain ⟨z, c, hz, hcm⟩ := hp.exists_lift_map_eq_eqToHom_comp m
  have hcab : c ≫ a = c ≫ b := (H c).2 ⟨eqToHom hz, hcm.symm⟩
  refine ⟨⟨⟨Fork.ofι c hcab, Fork.IsLimit.mk' _ fun s => ?_⟩⟩⟩
  have hk := ((H s.ι).1 s.condition).choose_spec
  set k := ((H s.ι).1 s.condition).choose
  have hf : (k ≫ eqToHom hz.symm) ≫ p.map c = p.map s.ι := by simp [hcm, hk]
  have hu := hp.unique_lift c s.ι _ hf
  refine ⟨hu.exists.choose, hu.exists.choose_spec.2,
    fun {l} hl => hu.unique ⟨?_, hl⟩ hu.exists.choose_spec⟩
  have hl' : (p.map l ≫ eqToHom hz) ≫ m = k ≫ m := by
    rw [hk, Category.assoc, ← hcm, ← p.map_comp]
    exact congrArg p.map hl
  rw [← (cancel_mono m).1 hl']
  simp

/-- The reduction of Stacks 06WY (2) to an automorphism: the morphisms `t` into `x` with
`t ≫ a = t ≫ b` are those whose image in the base factors through a monomorphism, as soon as this
holds for each pair `(i, 𝟙)` with `i` an automorphism of an object in its fibre. -/
theorem exists_locus_of_automorphism [HasEqualizers 𝒞]
    (H : ∀ (x' : 𝒳) (i : x' ⟶ x'), p.map i = 𝟙 _ →
      ∃ (M : 𝒞) (m : M ⟶ p.obj x'), Mono m ∧
        ∀ ⦃w : 𝒳⦄ (t : w ⟶ x'), t ≫ i = t ↔ ∃ k, k ≫ m = p.map t)
    {x y : 𝒳} (a b : x ⟶ y) :
    ∃ (M : 𝒞) (m : M ⟶ p.obj x), Mono m ∧
      ∀ ⦃w : 𝒳⦄ (t : w ⟶ x), t ≫ a = t ≫ b ↔ ∃ k, k ≫ m = p.map t := by
  let ι := equalizer.ι (p.map a) (p.map b)
  obtain ⟨x', c, hx', hcι⟩ := hp.exists_lift_map_eq_eqToHom_comp ι
  have hab : 𝟙 _ ≫ p.map (c ≫ a) = p.map (c ≫ b) := by
    rw [Category.id_comp, p.map_comp, p.map_comp, hcι, Category.assoc, Category.assoc,
      equalizer.condition]
  obtain ⟨i, ⟨hip, hi⟩, -⟩ := hp.unique_lift (c ≫ a) (c ≫ b) _ hab
  obtain ⟨M, m', hm', H'⟩ := H x' i hip
  have : Mono (p.map c) := by
    rw [hcι]
    infer_instance
  refine ⟨M, m' ≫ p.map c, mono_comp _ _, fun w t => ?_⟩
  constructor
  · intro ht
    let q := equalizer.lift (f := p.map a) (g := p.map b) (p.map t)
      (by rw [← p.map_comp, ← p.map_comp, ht])
    have hf : (q ≫ eqToHom hx'.symm) ≫ p.map c = p.map t := by simp [hcι, q, ι]
    obtain ⟨t', ⟨-, ht'⟩, -⟩ := hp.unique_lift c t _ hf
    have e1 : t' = t' ≫ i := by
      refine (hp.unique_lift (c ≫ a) (t' ≫ c ≫ a) (p.map t') (by simp)).unique ⟨rfl, rfl⟩
        ⟨by simp [hip], ?_⟩
      rw [Category.assoc, hi]
      simpa only [← Category.assoc, ht'] using ht.symm
    obtain ⟨k, hk⟩ := (H' t').1 e1.symm
    exact ⟨k, by rw [← Category.assoc, hk, ← p.map_comp, ht']⟩
  · rintro ⟨k, hk⟩
    have hf : (k ≫ m') ≫ p.map c = p.map t := by simpa using hk
    obtain ⟨t', ⟨ht'p, ht'⟩, -⟩ := hp.unique_lift c t _ hf
    have e1 := (H' t').2 ⟨k, ht'p.symm⟩
    rw [← ht']
    simp only [Category.assoc]
    rw [← hi, reassoc_of% e1]

variable [p.IsFibered]

/-- For an automorphism `i` of an object `x` of the fibre over `U`, the morphisms `t` into `x`
over `g : T ⟶ U` with `t ≫ i = t` are those for which `g` factors through a monomorphism, provided
the presheaf `Mor(x, x)` of Stacks 02ZB has representable equalizer loci: the locus is the one
where the two sections `id` and `i` of `Mor(x, x)` agree. -/
theorem exists_locus_of_morPresheaf {U : 𝒞} (x : p.Fiber U)
    (hx : Presheaf.HasRepresentableEqualizerLoci (p.morPresheaf x x)) (i : x ⟶ x) :
    ∃ (M : 𝒞) (m : M ⟶ U), Mono m ∧
      ∀ ⦃T : 𝒞⦄ (g : T ⟶ U) ⦃w : 𝒳⦄ (t : w ⟶ x.1) [p.IsHomLift g t],
        t ≫ i.1 = t ↔ ∃ k, k ≫ m = g := by
  let π₁ := IsPreFibered.pullbackMap x.2 (𝟙 U)
  have : p.IsHomLift (𝟙 U) π₁ :=
    inferInstanceAs (p.IsHomLift (𝟙 U) (IsPreFibered.pullbackMap x.2 (𝟙 U)))
  have : p.IsHomLift (𝟙 U) i.1 := i.2
  have : p.IsHomLift (𝟙 U) (π₁ ≫ i.1) := inferInstance
  let χ := IsCartesian.map p (𝟙 U) π₁ (π₁ ≫ i.1)
  have hχ : χ ≫ π₁ = π₁ ≫ i.1 := IsCartesian.fac p (𝟙 U) π₁ (π₁ ≫ i.1)
  let s₂ : (p.morPresheaf x x).obj (op (Over.mk (𝟙 U))) := ⟨χ, IsCartesian.map_isHomLift _ _ _ _⟩
  let s₁ : (p.morPresheaf x x).obj (op (Over.mk (𝟙 U))) := 𝟙 _
  obtain ⟨M, m, hm, H⟩ := hx s₁ s₂
  have hm' : m.left = M.hom := by simpa using Over.w m
  have key : ∀ ⦃T : 𝒞⦄ (g : T ⟶ U) ⦃w : 𝒳⦄ (t : w ⟶ x.1) [p.IsHomLift g t],
      (p.morPresheaf x x).map (Over.homMk g : Over.mk g ⟶ Over.mk (𝟙 U)).op s₁ =
        (p.morPresheaf x x).map (Over.homMk g : Over.mk g ⟶ Over.mk (𝟙 U)).op s₂ ↔
          t ≫ i.1 = t := by
    intro T g w t _
    let hV : Over.mk g ⟶ Over.mk (𝟙 U) := Over.homMk g
    let πV : (pullbackFiber p x g).1 ⟶ x.1 := IsPreFibered.pullbackMap x.2 g
    have : p.IsStronglyCartesian g t := hp.isStronglyCartesian_homLift g t
    have : p.IsStronglyCartesian g πV := hp.isStronglyCartesian_homLift g πV
    have transfer : ∀ {w₁ w₂ : 𝒳} (t₁ : w₁ ⟶ x.1) (t₂ : w₂ ⟶ x.1)
        [p.IsStronglyCartesian g t₁] [p.IsStronglyCartesian g t₂],
        t₁ ≫ i.1 = t₁ → t₂ ≫ i.1 = t₂ := by
      intro w₁ w₂ t₁ t₂ _ _ h
      rw [← IsStronglyCartesian.fac p g t₁ (f' := g) (g := 𝟙 T) (Category.id_comp g).symm t₂,
        Category.assoc, h]
    have hchain : pullbackFiberMap p x hV ≫ χ ≫ π₁ = πV ≫ i.1 := by
      rw [hχ, ← Category.assoc]
      exact congrArg (· ≫ i.1) (pullbackFiberMap_fac p x hV)
    show morRestrict p x x hV s₁ = morRestrict p x x hV s₂ ↔ _
    rw [show s₁ = 𝟙 _ from rfl, morRestrict_id_hom]
    constructor
    · intro h
      have h' : πV ≫ i.1 = πV := by
        rw [← (morRestrict_fac p x x hV s₂).trans hchain, ← h]
        exact Category.id_comp πV
      exact transfer πV t h'
    · intro h
      exact morRestrict_uniq p x x hV s₂ _
        ((Category.id_comp πV).trans ((transfer t πV h).symm.trans hchain.symm))
  have : Mono M.hom := by
    rw [← hm']
    infer_instance
  refine ⟨M.left, M.hom, this, fun T g w t _ => ?_⟩
  rw [← key g t, H]
  constructor
  · rintro ⟨k, -⟩
    exact ⟨k.left, by simp⟩
  · rintro ⟨k, hk⟩
    exact ⟨Over.homMk k (by simpa using hk), by ext; simp [hm', hk]⟩

/-- For an automorphism `i` of an object `x` lying over the identity of `p x`, the morphisms `t`
into `x` with `t ≫ i = t` are those whose image in the base factors through a monomorphism,
provided the presheaf `Mor(x, x)` of Stacks 02ZB has representable equalizer loci. -/
theorem exists_locus_of_morPresheaf' (x : 𝒳)
    (hx : Presheaf.HasRepresentableEqualizerLoci
      (p.morPresheaf (Fiber.mk (rfl : p.obj x = p.obj x))
        (Fiber.mk (rfl : p.obj x = p.obj x))))
    (i : x ⟶ x) (hi : p.map i = 𝟙 _) :
    ∃ (M : 𝒞) (m : M ⟶ p.obj x), Mono m ∧
      ∀ ⦃w : 𝒳⦄ (t : w ⟶ x), t ≫ i = t ↔ ∃ k, k ≫ m = p.map t := by
  have : p.IsHomLift (𝟙 (p.obj x)) i := by
    rw [← hi]
    infer_instance
  obtain ⟨M, m, hm, H⟩ := hp.exists_locus_of_morPresheaf (Fiber.mk rfl) hx
    (Fiber.homMk p (p.obj x) i)
  exact ⟨M, m, hm, fun w t => @H _ (p.map t) _ t (IsHomLift.map (p := p) t)⟩

/-- **The criterion of Stacks 06WY (2).** A category fibred in groupoids over a category with
equalizers has equalizers if, for every object `x` lying over `U`, any two sections of the
presheaf `Mor(x, x)` of Stacks 02ZB agree exactly over a representable locus. -/
theorem hasEqualizers_of_morPresheaf [HasEqualizers 𝒞]
    (h : ∀ (U : 𝒞) (x : p.Fiber U),
      Presheaf.HasRepresentableEqualizerLoci (p.morPresheaf x x)) :
    HasEqualizers 𝒳 := by
  have : ∀ {x y : 𝒳} {a b : x ⟶ y}, HasLimit (parallelPair a b) := fun {x y} {a b} => by
    obtain ⟨M, m, hm, H⟩ := hp.exists_locus_of_automorphism
      (fun x' i hi => hp.exists_locus_of_morPresheaf' x' (h _ _) i hi) a b
    exact hp.hasLimit_parallelPair_of_locus a b m H
  exact hasEqualizers_of_hasLimit_parallelPair 𝒳

end Functor.IsFiberedInGroupoids

end CategoryTheory
