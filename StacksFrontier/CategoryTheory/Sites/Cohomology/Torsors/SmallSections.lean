module

public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Logic.Small.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TrivialityAndGlobalSections

/-!
# The sections of a pseudo-torsor are no bigger than the sections of the group

Let `(C, J)` be a site, let `𝒢` be a sheaf of groups on it with sections in `Type w`, and let
`F` be a pseudo-torsor under `𝒢` whose sections are allowed to live in an arbitrary universe
`Type t`. Over an object `U` with a section `s` of `F`, the orbit map `g ↦ g · s` is a
bijection from the sections of `𝒢` over `U` onto the sections of `F` over `U`, because the
action is simply transitive there; over an object with no section the set of sections is empty.
Either way the sections of `F` over `U` are `w`-small, so `F` is carried by a pseudo-torsor
whose sections live in `Type w`, the universe of the sections of `𝒢`.

## Main definitions

* `PseudoTorsor.sectionEquivGroup`: over an object carrying a section, the orbit map is a
  bijection from the sections of the sheaf of groups onto the sections of the pseudo-torsor.
* `PseudoTorsor.ofNatEquiv`: a pseudo-torsor transported onto a presheaf identified with its
  underlying presheaf by a natural family of bijections, possibly into another universe.
* `PseudoTorsor.shrinkPresheaf` and `PseudoTorsor.shrink`: the underlying presheaf of a
  pseudo-torsor replaced by a `Type w`-valued model of it, and the pseudo-torsor it carries.
* `PseudoTorsor.shrinkEquiv` and `PseudoTorsor.shrinkNatIso`: the comparison between the
  shrunk pseudo-torsor and the original one, as a family of bijections on sections and as an
  isomorphism of presheaves with values in `Type (max w t)`.

## Main results

* `PseudoTorsor.small_presheaf_obj`: the sections of a pseudo-torsor over any object form a
  `w`-small type, `w` being the universe of the sections of the sheaf of groups. No
  nonemptiness is assumed: an object over which the pseudo-torsor has no section is allowed.
* `PseudoTorsor.isTorsor_ofNatEquiv` and `PseudoTorsor.shrink_isTorsor`: the transport and the
  shrinking preserve the torsor condition.
* `PseudoTorsor.shrinkEquiv_act` and `PseudoTorsor.shrinkEquiv_map`: the comparison is
  equivariant and natural, so the shrunk pseudo-torsor carries the same action.

## Implementation notes

The transport `PseudoTorsor.ofNatEquiv` takes the target presheaf as an argument rather than
building it, so that a client who already has the presheaf it wants the pseudo-torsor to be
carried by — a sheaf of sections of an algebraic space, say — obtains a pseudo-torsor on that
very presheaf, with no further comparison isomorphism to thread through. The shrinking is the
instance of it at `CategoryTheory.Shrink` of the sections.

A pseudo-torsor and its shrinking have presheaves with values in different universes, so they
cannot be compared by a morphism of pseudo-torsors; the comparison is recorded as the family
of bijections `PseudoTorsor.shrinkEquiv` on sections, with its equivariance and its
naturality, and `PseudoTorsor.shrinkNatIso` assembles it into an isomorphism of presheaves
after lifting both sides to `Type (max w t)`.

The sheaf condition travels along the comparison because the type-valued sheaf condition is
invariant under a natural family of bijections, which is
`CategoryTheory.Presieve.isSheaf_iff_of_nat_equiv`, and that lemma does not require the two
presheaves to have values in the same universe.

## References

* [Stacks Project, Tag 03AH](https://stacks.math.columbia.edu/tag/03AH)
-/

@[expose] public section

open CategoryTheory Opposite

universe r t w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {𝒢 : SheafOfGroups.{w} (C := C) J}

namespace PseudoTorsor

/-- Over an object `U` carrying a section `s` of a pseudo-torsor `F` under `𝒢`, the orbit map
`g ↦ g · s` is a bijection from the sections of `𝒢` over `U` onto the sections of `F` over
`U`: it is surjective because the action of `𝒢(U)` on `F(U)` is transitive, and injective
because the element of `𝒢(U)` carrying `s` to a given section is unique. -/
noncomputable def sectionEquivGroup (F : PseudoTorsor.{t} 𝒢) (U : Cᵒᵖ)
    (s : F.presheaf.obj U) : 𝒢.presheaf.obj U ≃ F.presheaf.obj U where
  toFun g := F.act U g s
  invFun x := (F.simplyTransitive U ⟨s⟩ s x).choose
  left_inv g := ((F.simplyTransitive U ⟨s⟩ s (F.act U g s)).choose_spec.2 g rfl).symm
  right_inv x := (F.simplyTransitive U ⟨s⟩ s x).choose_spec.1

/-- The orbit map of `PseudoTorsor.sectionEquivGroup` is the action on the chosen section. -/
@[simp]
theorem sectionEquivGroup_apply (F : PseudoTorsor.{t} 𝒢) (U : Cᵒᵖ) (s : F.presheaf.obj U)
    (g : 𝒢.presheaf.obj U) : F.sectionEquivGroup U s g = F.act U g s :=
  rfl

/-- The sections of a pseudo-torsor under `𝒢` over an object are no bigger than the sections of
`𝒢` over that object: over an object carrying a section they are in bijection with them by
`PseudoTorsor.sectionEquivGroup`, and over an object carrying none they are empty. -/
theorem small_presheaf_obj (F : PseudoTorsor.{t} 𝒢) (U : Cᵒᵖ) :
    Small.{w} (F.presheaf.obj U) := by
  by_cases h : Nonempty (F.presheaf.obj U)
  · exact Small.mk' (F.sectionEquivGroup U h.some).symm
  · exact small_of_injective (β := 𝒢.presheaf.obj U) (f := fun x => (h ⟨x⟩).elim)
      fun x _ _ => (h ⟨x⟩).elim

attribute [local instance] small_presheaf_obj

/-- A pseudo-torsor `F` under `𝒢` transported onto a presheaf `Q` identified with the
underlying presheaf of `F` by a family of bijections `e` natural in the object: the sections of
`Q` are acted on through `e`. The values of `Q` need not lie in the universe of the values of
the underlying presheaf of `F`; the sheaf condition travels along `e` all the same. -/
noncomputable def ofNatEquiv (F : PseudoTorsor.{t} 𝒢) (Q : Cᵒᵖ ⥤ Type r)
    (e : ∀ U, Q.obj U ≃ F.presheaf.obj U)
    (he : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (x : Q.obj U),
      e V (Q.map f x) = F.presheaf.map f (e U x)) :
    PseudoTorsor.{r} 𝒢 where
  presheaf := Q
  isSheaf := by
    rw [CategoryTheory.isSheaf_iff_isSheaf_of_type,
      Presieve.isSheaf_iff_of_nat_equiv (P₁ := Q) (P₂ := F.presheaf)
        (fun ⦃X⦄ => e (op X)) (fun ⦃X Y⦄ f x => he f.op x),
      ← CategoryTheory.isSheaf_iff_isSheaf_of_type]
    exact F.isSheaf
  act U g x := (e U).symm (F.act U g (e U x))
  one_act U x := by rw [F.one_act, Equiv.symm_apply_apply]
  mul_act U g h x := by simp only [Equiv.apply_symm_apply, F.mul_act]
  naturality f g x := by
    apply (e _).injective
    simp only [he, Equiv.apply_symm_apply]
    exact F.naturality f g (e _ x)
  simplyTransitive U hne x y := by
    obtain ⟨z⟩ := hne
    obtain ⟨g, hg, hgu⟩ := F.simplyTransitive U ⟨e U z⟩ (e U x) (e U y)
    refine ⟨g, (e U).injective ?_, fun g' hg' => hgu g' ?_⟩
    · rw [Equiv.apply_symm_apply, hg]
    · rw [← hg', Equiv.apply_symm_apply]

/-- The underlying presheaf of a transported pseudo-torsor is the prescribed presheaf. -/
@[simp]
theorem presheaf_ofNatEquiv (F : PseudoTorsor.{t} 𝒢) (Q : Cᵒᵖ ⥤ Type r)
    (e : ∀ U, Q.obj U ≃ F.presheaf.obj U)
    (he : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (x : Q.obj U),
      e V (Q.map f x) = F.presheaf.map f (e U x)) :
    (F.ofNatEquiv Q e he).presheaf = Q :=
  rfl

/-- The action of a transported pseudo-torsor is the action of the original one, read through
the identification of the sections. -/
theorem act_ofNatEquiv (F : PseudoTorsor.{t} 𝒢) (Q : Cᵒᵖ ⥤ Type r)
    (e : ∀ U, Q.obj U ≃ F.presheaf.obj U)
    (he : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (x : Q.obj U),
      e V (Q.map f x) = F.presheaf.map f (e U x))
    (U : Cᵒᵖ) (g : 𝒢.presheaf.obj U) (x : Q.obj U) :
    (F.ofNatEquiv Q e he).act U g x = (e U).symm (F.act U g (e U x)) :=
  rfl

/-- A transported pseudo-torsor is locally nonempty exactly when the original one is: the
identification of the sections is a bijection over every object. -/
theorem isTorsor_ofNatEquiv (F : PseudoTorsor.{t} 𝒢) (Q : Cᵒᵖ ⥤ Type r)
    (e : ∀ U, Q.obj U ≃ F.presheaf.obj U)
    (he : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (x : Q.obj U),
      e V (Q.map f x) = F.presheaf.map f (e U x)) :
    (F.ofNatEquiv Q e he).IsTorsor ↔ F.IsTorsor := by
  refine ⟨fun h U => ?_, fun h U => ?_⟩ <;> obtain ⟨S, hS, hne⟩ := h U
  · exact ⟨S, hS, fun _ _ hf => ⟨e _ (hne hf).some⟩⟩
  · exact ⟨S, hS, fun _ _ hf => ⟨(e _).symm (hne hf).some⟩⟩

/-- The underlying presheaf of a pseudo-torsor under `𝒢`, replaced section-wise by a model of
it in the universe `Type w` of the sections of `𝒢`. -/
noncomputable def shrinkPresheaf (F : PseudoTorsor.{t} 𝒢) : Cᵒᵖ ⥤ Type w where
  obj U := Shrink.{w} (F.presheaf.obj U)
  map {U V} f := ↾(fun (x : Shrink.{w} (F.presheaf.obj U)) =>
    equivShrink.{w} (F.presheaf.obj V)
      (F.presheaf.map f ((equivShrink.{w} (F.presheaf.obj U)).symm x)))
  map_id U := by
    ext x
    simp
  map_comp f g := by
    ext x
    simp

/-- The sections of `PseudoTorsor.shrinkPresheaf` over an object. -/
theorem shrinkPresheaf_obj (F : PseudoTorsor.{t} 𝒢) (U : Cᵒᵖ) :
    F.shrinkPresheaf.obj U = Shrink.{w} (F.presheaf.obj U) :=
  rfl

/-- The restriction maps of `PseudoTorsor.shrinkPresheaf`. -/
theorem shrinkPresheaf_map (F : PseudoTorsor.{t} 𝒢) {U V : Cᵒᵖ} (f : U ⟶ V)
    (x : Shrink.{w} (F.presheaf.obj U)) :
    F.shrinkPresheaf.map f x =
      equivShrink.{w} (F.presheaf.obj V) (F.presheaf.map f ((equivShrink.{w} _).symm x)) :=
  rfl

/-- The identification of the sections of `PseudoTorsor.shrinkPresheaf` with the sections of
the underlying presheaf of the pseudo-torsor is natural in the object. -/
theorem shrinkPresheaf_naturality (F : PseudoTorsor.{t} 𝒢) {U V : Cᵒᵖ} (f : U ⟶ V)
    (x : F.shrinkPresheaf.obj U) :
    (equivShrink.{w} (F.presheaf.obj V)).symm (F.shrinkPresheaf.map f x) =
      F.presheaf.map f ((equivShrink.{w} (F.presheaf.obj U)).symm x) :=
  (equivShrink.{w} (F.presheaf.obj V)).symm_apply_apply
    (F.presheaf.map f ((equivShrink.{w} (F.presheaf.obj U)).symm x))

/-- A pseudo-torsor under `𝒢` carried by a presheaf with values in the universe `Type w` of
the sections of `𝒢`, whatever the universe of the sections of the given one. -/
noncomputable def shrink (F : PseudoTorsor.{t} 𝒢) : PseudoTorsor.{w} 𝒢 :=
  F.ofNatEquiv F.shrinkPresheaf (fun U => (equivShrink.{w} (F.presheaf.obj U)).symm)
    fun f x => F.shrinkPresheaf_naturality f x

/-- The underlying presheaf of the shrinking of a pseudo-torsor. -/
theorem shrink_presheaf (F : PseudoTorsor.{t} 𝒢) : F.shrink.presheaf = F.shrinkPresheaf :=
  rfl

/-- The comparison between the sections of the shrinking of a pseudo-torsor over an object and
the sections of the pseudo-torsor itself over that object. -/
noncomputable def shrinkEquiv (F : PseudoTorsor.{t} 𝒢) (U : Cᵒᵖ) :
    F.shrink.presheaf.obj U ≃ F.presheaf.obj U :=
  (equivShrink.{w} (F.presheaf.obj U)).symm

/-- The action of the shrinking of a pseudo-torsor, read through the comparison of the
sections. -/
theorem shrink_act (F : PseudoTorsor.{t} 𝒢) (U : Cᵒᵖ) (g : 𝒢.presheaf.obj U)
    (x : F.shrink.presheaf.obj U) :
    F.shrink.act U g x = (F.shrinkEquiv U).symm (F.act U g (F.shrinkEquiv U x)) :=
  rfl

/-- The comparison of the sections of the shrinking of a pseudo-torsor with the sections of the
pseudo-torsor is equivariant: the shrinking carries the same action. -/
@[simp]
theorem shrinkEquiv_act (F : PseudoTorsor.{t} 𝒢) (U : Cᵒᵖ) (g : 𝒢.presheaf.obj U)
    (x : F.shrink.presheaf.obj U) :
    F.shrinkEquiv U (F.shrink.act U g x) = F.act U g (F.shrinkEquiv U x) :=
  (F.shrinkEquiv U).apply_symm_apply (F.act U g (F.shrinkEquiv U x))

/-- The comparison of the sections of the shrinking of a pseudo-torsor with the sections of the
pseudo-torsor is natural in the object. -/
@[simp]
theorem shrinkEquiv_map (F : PseudoTorsor.{t} 𝒢) {U V : Cᵒᵖ} (f : U ⟶ V)
    (x : F.shrink.presheaf.obj U) :
    F.shrinkEquiv V (F.shrink.presheaf.map f x) = F.presheaf.map f (F.shrinkEquiv U x) :=
  F.shrinkPresheaf_naturality f x

/-- The shrinking of a pseudo-torsor is locally nonempty exactly when the pseudo-torsor is, so
the shrinking of a torsor is a torsor. -/
theorem shrink_isTorsor (F : PseudoTorsor.{t} 𝒢) : F.shrink.IsTorsor ↔ F.IsTorsor :=
  F.isTorsor_ofNatEquiv F.shrinkPresheaf (fun U => (equivShrink.{w} (F.presheaf.obj U)).symm)
    fun f x => F.shrinkPresheaf_naturality f x

/-- The isomorphism between the shrinking of a pseudo-torsor and the pseudo-torsor itself,
their underlying presheaves being lifted to presheaves with values in `Type (max w t)` so that
they may be compared at all. -/
noncomputable def shrinkNatIso (F : PseudoTorsor.{t} 𝒢) :
    F.shrink.presheaf ⋙ uliftFunctor.{t, w} ≅ F.presheaf ⋙ uliftFunctor.{w, t} :=
  NatIso.ofComponents
    (fun U => (Equiv.ulift.trans ((F.shrinkEquiv U).trans Equiv.ulift.symm)).toIso)
    fun f => by
      ext x
      exact congrArg ULift.up (F.shrinkEquiv_map f x.down)

end PseudoTorsor

end
