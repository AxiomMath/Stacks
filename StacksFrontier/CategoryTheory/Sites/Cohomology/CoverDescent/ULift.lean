module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.CoverDescent.Cohomology

/-!
# Representable covers in a larger universe

`Stacks.Sites.CoverDescent.IsClosedUnderRepresentableCovers` is a condition on a class of
presheaves of sets with values in one universe, and the two conclusions of the descent it feeds —
`Stacks.Sites.CoverDescent.restrictHom_bijective_of_mem` and
`Stacks.Sites.CoverDescent.ext_restriction_eq_zero_of_mem` — are about sheaves in that universe.
This file moves a class closed under representable covers up to any larger universe, by
composing its members with `uliftFunctor`, so that the descent applies to sheaves with values in
the larger universe.

The three ingredients are that `uliftYoneda` at the larger universe is `uliftYoneda` at the
smaller one followed by `uliftFunctor`, that whiskering by `uliftFunctor` preserves local
surjectivity, and that the tuple presheaves of a whiskered map are the whiskered tuple
presheaves.

## Main definitions

* `Stacks.Sites.CoverDescent.liftClass`: the presheaves isomorphic to a member of a class
  composed with `uliftFunctor`.

## Main results

* `Stacks.Sites.CoverDescent.IsClosedUnderRepresentableCovers.liftClass`: closure under
  representable covers passes to the lifted class.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe t w v u₁ u₂

namespace Stacks.Sites.CoverDescent

variable {C : Type u₁} [Category.{v} C]

/-- **Whiskering by `uliftFunctor` preserves local surjectivity.** The image sieve of a section
`s` of the whiskered map is the image sieve of `s.down`. -/
theorem isLocallySurjective_whiskerRight_uliftFunctor (J : GrothendieckTopology C)
    {A P : Cᵒᵖ ⥤ Type w} (f : A ⟶ P) [Presheaf.IsLocallySurjective J f] :
    Presheaf.IsLocallySurjective J (Functor.whiskerRight f uliftFunctor.{t}) where
  imageSieve_mem {U} s := by
    refine J.superset_covering ?_ (Presheaf.imageSieve_mem J f s.down)
    rintro V i ⟨a, ha⟩
    exact ⟨ULift.up a, congrArg ULift.up ha⟩

/-- The tuple presheaves of a map whiskered by `uliftFunctor` are its tuple presheaves whiskered
by `uliftFunctor`. -/
def tuplePresheafWhiskerRightUliftIso {A P : Cᵒᵖ ⥤ Type w} (f : A ⟶ P) (r : ℕ) :
    tuplePresheaf (Functor.whiskerRight f uliftFunctor.{t}) r ≅
      tuplePresheaf f r ⋙ uliftFunctor.{t} where
  hom :=
    { app := fun y => ↾fun a => ULift.up ⟨fun i => (a.1 i).down,
        fun i => congrArg ULift.down (a.2 i)⟩
      naturality := fun _ _ _ => rfl }
  inv :=
    { app := fun y => ↾fun b => ⟨fun i => ULift.up (b.down.1 i),
        fun i => congrArg ULift.up (b.down.2 i)⟩
      naturality := fun _ _ _ => rfl }

/-- `uliftYoneda` at a larger universe is `uliftYoneda` at a smaller one followed by
`uliftFunctor`. -/
def uliftYonedaObjIsoComp (X : C) :
    uliftYoneda.{max w t}.obj X ≅ uliftYoneda.{w}.obj X ⋙ uliftFunctor.{t} :=
  NatIso.ofComponents (fun _ => Equiv.toIso
    { toFun := fun a => ULift.up (ULift.up a.down)
      invFun := fun b => ULift.up b.down.down
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl })
    (fun _ => rfl)

/-- **A class of presheaves of sets, moved to a larger universe.** The presheaves with values in
`Type (max v w t)` isomorphic to a member of `𝔎` composed with `uliftFunctor`. -/
def liftClass (𝔎 : (Cᵒᵖ ⥤ Type (max v w)) → Prop) : (Cᵒᵖ ⥤ Type (max v w t)) → Prop :=
  fun P => ∃ Q, 𝔎 Q ∧ Nonempty (P ≅ Q ⋙ uliftFunctor.{t})

variable {D : Type u₂} [Category.{v} D] {J : GrothendieckTopology C}
  {K : GrothendieckTopology D} {u : D ⥤ C} [u.IsContinuous K J] [u.Full] [u.Faithful]

omit [u.IsContinuous K J] [u.Full] [u.Faithful] in
/-- **Closure under representable covers passes to a larger universe.** If `𝔎` is closed under
representable covers, so is the class of presheaves isomorphic to a member of `𝔎` followed by
`uliftFunctor`: the representable cover of a member, whiskered by `uliftFunctor`, is a
representable cover of its lift, with the lifted tuple presheaves. -/
theorem IsClosedUnderRepresentableCovers.liftClass {𝔎 : (Cᵒᵖ ⥤ Type (max v w)) → Prop}
    (h𝔎 : IsClosedUnderRepresentableCovers.{w} J K u 𝔎) :
    IsClosedUnderRepresentableCovers.{max w t} J K u
      (Stacks.Sites.CoverDescent.liftClass.{t} 𝔎) := by
  rintro P ⟨Q, hQ, ⟨e⟩⟩
  obtain ⟨d, tQ, ht, htK, htup⟩ := h𝔎 Q hQ
  let ι := uliftYonedaObjIsoComp.{t, w} (u.obj d)
  refine ⟨d, ι.hom ≫ Functor.whiskerRight tQ uliftFunctor.{t} ≫ e.inv, ?_, ?_, fun r => ?_⟩
  · have := isLocallySurjective_whiskerRight_uliftFunctor.{t} J tQ
    infer_instance
  · have := isLocallySurjective_whiskerRight_uliftFunctor.{t} K (Functor.whiskerLeft u.op tQ)
    change Presheaf.IsLocallySurjective K (Functor.whiskerLeft u.op ι.hom ≫
      Functor.whiskerRight (Functor.whiskerLeft u.op tQ) uliftFunctor.{t} ≫
        Functor.whiskerLeft u.op e.inv)
    infer_instance
  · obtain ⟨Q', hQ', ⟨e'⟩⟩ := htup r
    exact ⟨Q' ⋙ uliftFunctor.{t}, ⟨Q', hQ', ⟨Iso.refl _⟩⟩,
      ⟨tuplePresheafCompIso ι _ e.symm (r + 1) ≪≫
        tuplePresheafWhiskerRightUliftIso.{t} tQ (r + 1) ≪≫
          Functor.isoWhiskerRight e' uliftFunctor.{t}⟩⟩

end Stacks.Sites.CoverDescent

end
