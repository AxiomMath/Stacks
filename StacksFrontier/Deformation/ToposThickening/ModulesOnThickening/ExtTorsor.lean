module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import Mathlib.CategoryTheory.Abelian.Refinements
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.YonedaExtOne

/-!
# Extensions, their `Ext` classes, and the torsor they form

This file collects what is needed about `Ext` classes of short exact sequences in an abelian
category, and the one piece of elementary algebra that turns a coset of the range of an
injective additive map into a torsor. Nothing here mentions sheaves.

The facts about `Ext` are: a short exact sequence may be pulled back along a map into its
quotient term and stays short exact; two short exact sequences whose classes differ by a map of
quotient terms are related by a map of middle terms; and for a fully faithful exact functor the
induced map on `Ext¹` is injective, with the class of an extension lying in its range as soon as
the middle term of that extension lies in the essential image.

## Main definitions

* `AddTorsor.ofAddMonoidHomTranslate`: a translate of the range of an injective additive
  homomorphism, described by a predicate, is a torsor under its domain.

## Main results

* `CategoryTheory.ShortComplex.ShortExact.shortExact_pullbackSnd`: the base change of a short
  exact sequence along a map into its quotient term.
* `CategoryTheory.ShortComplex.ShortExact.exists_hom_of_extClass_eq`: if the `Ext` class of one
  short exact sequence is the class of a second composed with a map of quotient terms, the two
  sequences are related by a morphism of their middle terms over that map.
* `CategoryTheory.Functor.mapExtAddHom_injective_of_fullyFaithful` and
  `CategoryTheory.Functor.exists_mapExtAddHom_eq_of_essImage`: injectivity of the map induced on
  `Ext¹` by a fully faithful exact functor, and the criterion for a class to be in its range.

## Implementation notes

`shortExact_pullbackSnd` is a transposed and more general form of
`Deformation.ToposThickening.differencePullback_shortExact`
(`StacksFrontier/Deformation/ToposThickening/ExtensionDifference.lean`), which states the same fact
for the pullback of the two legs in the other order and only for a map of the special shape
`S₁.g ≫ φ`. The two are not interchangeable without transporting along
`CategoryTheory.Limits.pullbackSymmetry` and rewriting under `pullback`, so both exist; the
general statement is the one here, and the proof follows the pattern of the other.

Both `Ext` statements about a functor `F` ask for `F` to be additive, to preserve finite limits
and finite colimits, and to be full and faithful. Fullness and faithfulness enter only through
`CategoryTheory.Functor.preimageIso` and `CategoryTheory.Functor.map_injective`, so no exactness
of an inverse is used.

## References

* [Stacks Project, Tag 06XV](https://stacks.math.columbia.edu/tag/06XV)
* [Stacks Project, Tag 08ME](https://stacks.math.columbia.edu/tag/08ME)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe e v u v' u'

namespace CategoryTheory

namespace ShortComplex.ShortExact

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **Base change of a short exact sequence.** Pulling a short exact sequence back along a map
`u` into its quotient term gives a short exact sequence with the same kernel term and with the
source of `u` as quotient term. -/
lemma shortExact_pullbackSnd {S : ShortComplex C} (hS : S.ShortExact) {B : C} (u : B ⟶ S.X₃) :
    (ShortComplex.mk
      (pullback.lift S.f (0 : S.X₁ ⟶ B) (by simp)) (pullback.snd S.g u)
      (pullback.lift_snd _ _ _)).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  refine ShortComplex.ShortExact.mk' ?_ ?_ inferInstance
  · apply (ShortComplex.exact_iff_exact_up_to_refinements _).2
    intro A z hz
    dsimp only at z hz
    obtain ⟨y, hy⟩ := hS.exact.lift' (z ≫ pullback.fst S.g u) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hz, zero_comp])
    refine ⟨A, 𝟙 A, inferInstance, y, ?_⟩
    dsimp only
    rw [Category.id_comp]
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst]
      exact hy.symm
    · rw [Category.assoc, pullback.lift_snd, comp_zero]
      exact hz
  · exact mono_of_mono_fac (pullback.lift_fst S.f (0 : S.X₁ ⟶ B) (by simp))

variable [HasExt.{e} C]

/-- Two extensions have the same `Ext` class iff their middle terms are isomorphic compatibly
with the structure maps. -/
private lemma extClass_eq_iff_exists_iso {A B E E' : C} {i : A ⟶ E} {p : E ⟶ B}
    {w : i ≫ p = 0} {i' : A ⟶ E'} {p' : E' ⟶ B} {w' : i' ≫ p' = 0}
    (h : (ShortComplex.mk i p w).ShortExact) (h' : (ShortComplex.mk i' p' w').ShortExact) :
    h.extClass = h'.extClass ↔ ∃ φ : E ≅ E', i ≫ φ.hom = i' ∧ φ.hom ≫ p' = p :=
  (Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum C B A).2.1 E E' i p w i' p' w' h h'

/-- **Two short exact sequences with comparable `Ext` classes are comparable.** If the class of
`S` is the class of `T` composed with a map `β` of quotient terms, then there is a map of middle
terms which is the identity on the kernel term and `β` on the quotient term. -/
lemma exists_hom_of_extClass_eq {A B D E T : C} {f : A ⟶ E} {g : E ⟶ B} {w : f ≫ g = 0}
    {f' : A ⟶ T} {g' : T ⟶ D} {w' : f' ≫ g' = 0}
    (hS : (ShortComplex.mk f g w).ShortExact)
    (hT : (ShortComplex.mk f' g' w').ShortExact)
    (β : B ⟶ D)
    (h : hS.extClass = (Abelian.Ext.mk₀ β).comp hT.extClass (zero_add 1)) :
    ∃ v : E ⟶ T, f ≫ v = f' ∧ v ≫ g' = g ≫ β := by
  let P := ShortComplex.mk (pullback.lift f' (0 : A ⟶ B) (by simp [w']))
    (pullback.snd g' β) (pullback.lift_snd _ _ _)
  have hP : P.ShortExact := hT.shortExact_pullbackSnd β
  have hp : hP.extClass = (Abelian.Ext.mk₀ β).comp hT.extClass (zero_add 1) := by
    have hnat := hP.extClass_naturality hT
      { τ₁ := 𝟙 A, τ₂ := pullback.fst g' β, τ₃ := β
        comm₁₂ := by dsimp only [P]; rw [Category.id_comp, pullback.lift_fst]
        comm₂₃ := pullback.condition }
    change hP.extClass.comp (Abelian.Ext.mk₀ (𝟙 A)) (add_zero 1) =
      (Abelian.Ext.mk₀ β).comp hT.extClass (zero_add 1) at hnat
    rwa [Abelian.Ext.comp_mk₀_id] at hnat
  obtain ⟨v, hv, hv'⟩ := (extClass_eq_iff_exists_iso hS hP).1 (h.trans hp.symm)
  refine ⟨v.hom ≫ pullback.fst g' β, ?_, ?_⟩
  · rw [← Category.assoc, hv]
    exact pullback.lift_fst _ _ _
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hv']

end ShortComplex.ShortExact

namespace Functor

variable {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt.{e} C]
  {D : Type u'} [Category.{v', u'} D] [Abelian D] [HasExt.{e} D]

/-- The map induced on `Ext¹` sends the class of a short exact sequence to the class of its
image. -/
private lemma mapExtAddHom_extClass (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] {S : ShortComplex C} (hS : S.ShortExact) :
    F.mapExtAddHom S.X₃ S.X₁ 1 hS.extClass = (hS.map_of_exact F).extClass := by
  rw [Functor.mapExtAddHom_apply, Abelian.Ext.mapExactFunctor_extClass]

/-- **A fully faithful exact functor is injective on `Ext¹`.** Two classes with the same image
are represented by short exact sequences whose middle terms become isomorphic over the end terms
after applying the functor, hence are isomorphic already before. -/
lemma mapExtAddHom_injective_of_fullyFaithful (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.Full] [F.Faithful] (B A : C) :
    Function.Injective (F.mapExtAddHom B A 1) := by
  intro x y hxy
  obtain ⟨E, i, p, w, hE, hx⟩ :=
    (Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum C B A).1 x
  obtain ⟨E', i', p', w', hE', hy⟩ :=
    (Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum C B A).1 y
  let S : ShortComplex C := ShortComplex.mk i p w
  let S' : ShortComplex C := ShortComplex.mk i' p' w'
  have hS : S.ShortExact := hE
  have hS' : S'.ShortExact := hE'
  let T := S.map F
  let T' := S'.map F
  have hT : T.ShortExact := hS.map_of_exact F
  have hT' : T'.ShortExact := hS'.map_of_exact F
  have hmap : hT.extClass = hT'.extClass := by
    rwa [← hx, ← hy, mapExtAddHom_extClass F hS, mapExtAddHom_extClass F hS'] at hxy
  obtain ⟨φ, hφ₁, hφ₂⟩ := (ShortComplex.ShortExact.extClass_eq_iff_exists_iso hT hT').1 hmap
  have hφ₁' : i ≫ (F.preimageIso φ).hom = i' := F.map_injective <| by
    rwa [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage]
  have hφ₂' : (F.preimageIso φ).hom ≫ p' = p := F.map_injective <| by
    rwa [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage]
  exact hx.symm.trans <|
    ((ShortComplex.ShortExact.extClass_eq_iff_exists_iso hS hS').2
      ⟨F.preimageIso φ, hφ₁', hφ₂'⟩).trans hy

/-- **An extension in the essential image has an `Ext` class in the range.** If a class between
images of a fully faithful exact functor is represented by a short exact sequence whose middle
term is in the essential image, it is the image of a class upstairs. -/
lemma exists_mapExtAddHom_eq_of_essImage (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.Full] [F.Faithful]
    (B A : C) (ξ : Abelian.Ext (F.obj B) (F.obj A) 1)
    (hξ : ∃ (E : D) (i : F.obj A ⟶ E) (p : E ⟶ F.obj B) (w : i ≫ p = 0)
      (hE : (ShortComplex.mk i p w).ShortExact),
        hE.extClass = ξ ∧ F.essImage E) :
    ∃ η : Abelian.Ext B A 1, F.mapExtAddHom B A 1 η = ξ := by
  obtain ⟨E, iE, pE, wE, hE, hξE, hEss⟩ := hξ
  obtain ⟨M, ⟨e⟩⟩ := hEss
  let i : A ⟶ M := F.preimage (iE ≫ e.inv)
  let p : M ⟶ B := F.preimage (e.hom ≫ pE)
  have hi : F.map i ≫ e.hom = iE := by simp [i]
  have hp : e.hom ≫ pE = F.map p := by simp [p]
  have w : i ≫ p = 0 := F.map_injective <| by
    rw [Functor.map_comp, ← hp, ← Category.assoc, hi, wE, Functor.map_zero]
  let S : ShortComplex C := ShortComplex.mk i p w
  let SF := S.map F
  let T : ShortComplex D := ShortComplex.mk iE pE wE
  have h1 : 𝟙 _ ≫ T.f = SF.f ≫ e.hom := by simpa [T, SF] using hi.symm
  have h2 : e.hom ≫ T.g = SF.g ≫ 𝟙 _ := by simpa [T, SF] using hp
  let eSF : SF ≅ T := ShortComplex.isoMk (Iso.refl _) e (Iso.refl _) h1 h2
  have hSF : SF.ShortExact := ShortComplex.shortExact_of_iso eSF.symm hE
  have hS : S.ShortExact := ShortExact.reflects_shortExact_of_faithful F hSF
  refine ⟨hS.extClass, ?_⟩
  calc
    F.mapExtAddHom B A 1 hS.extClass = (hS.map_of_exact F).extClass :=
      mapExtAddHom_extClass F hS
    _ = hSF.extClass := by congr 1
    _ = hE.extClass := (ShortComplex.ShortExact.extClass_eq_iff_exists_iso hSF hE).2 ⟨e, hi, hp⟩
    _ = ξ := hξE

end Functor

end CategoryTheory

namespace AddTorsor

/-- **A translate of the range of an injective additive map is a torsor.** If a predicate `P` on
`B` cuts out `b + range f` for an injective `f : A →+ B`, then `{x // P x}` is a torsor under
`A`, with `a` acting by adding `f a`. -/
@[instance_reducible]
noncomputable def ofAddMonoidHomTranslate {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) (hf : Function.Injective f) (b : B) (P : B → Prop)
    (hP : ∀ x, P x ↔ ∃ a, b + f a = x) : AddTorsor A {x : B // P x} := by
  classical
  let Q := {x : B // P x}
  have hex (x y : Q) : ∃ d : A, f d = x.val - y.val := by
    obtain ⟨a, ha⟩ := (hP x.val).1 x.property
    obtain ⟨a', ha'⟩ := (hP y.val).1 y.property
    refine ⟨a - a', ?_⟩
    rw [map_sub, ← ha, ← ha']
    abel
  let δ (x y : Q) : A := Classical.choose (hex x y)
  have hδ (x y : Q) : f (δ x y) = x.val - y.val := Classical.choose_spec (hex x y)
  letI : AddAction A Q :=
    { vadd := fun a x => ⟨f a + x.val, (hP _).2 <| by
        obtain ⟨a', ha'⟩ := (hP x.val).1 x.property
        refine ⟨a + a', ?_⟩
        rw [map_add, ← ha']
        abel⟩
      zero_vadd := by
        intro x
        apply Subtype.ext
        change f 0 + x.val = x.val
        simp
      add_vadd := by
        intro a a' x
        apply Subtype.ext
        change f (a + a') + x.val = f a + (f a' + x.val)
        rw [map_add]
        abel }
  letI : VSub A Q := { vsub := δ }
  refine
    { nonempty := ⟨⟨b, (hP b).2 ⟨0, by simp⟩⟩⟩
      vsub_vadd' := ?_
      vadd_vsub' := ?_ }
  · intro x y
    apply Subtype.ext
    change f (δ x y) + y.val = x.val
    rw [hδ, sub_add_cancel]
  · intro a x
    apply hf
    change f (δ (a +ᵥ x) x) = f a
    rw [hδ]
    exact add_sub_cancel_right (f a) x.val

end AddTorsor

end
