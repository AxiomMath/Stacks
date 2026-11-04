module

public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Equalizers of formal coproducts

Let `C` be a category. The Stacks Project's category `SR(C)` of *semi-representable objects*
of `C` is Mathlib's `CategoryTheory.Limits.FormalCoproduct C`, whose objects are indexed
families of objects of `C`. Mathlib already constructs the terminal object, the arbitrary
coproducts and the pullbacks of `FormalCoproduct C`; this file constructs its equalizers.

A morphism `f : X ⟶ Y` of formal coproducts consists of a map `f.f : X.I → Y.I` of index
types together with components `f.φ i : X.obj i ⟶ Y.obj (f.f i)`. Two such morphisms `f`, `g`
can only be equalized over a component `i` of `X` where the index maps already agree, so the
equalizer of `f` and `g` is indexed by `{i : X.I // f.f i = g.f i}`, with component at such an
`i` the equalizer in `C` of `f.φ i` and `g.φ i`, the two being compared by the `eqToHom`
coming from `f.f i = g.f i`.

## Main definitions

* `CategoryTheory.Limits.FormalCoproduct.equalizerFork`: the fork of two morphisms of formal
  coproducts described above.

## Main results

* `CategoryTheory.Limits.FormalCoproduct.isLimitEqualizerFork`: that fork is an equalizer.
* `CategoryTheory.Limits.FormalCoproduct.instHasEqualizers`: **Stacks Project, Tag 01G2**,
  equalizers clause — if `C` has equalizers then so does `FormalCoproduct.{w} C`, i.e. the
  category of semi-representable objects of `C` has equalizers.

## Implementation notes

The construction is stated under `HasEqualizers C` and uses Mathlib's chosen `equalizer`
rather than taking an arbitrary family of component forks as data. Taking the forks as data
is possible but not usable in practice here: `FormalCoproduct.hom_ext`, which is how one
proves two morphisms of formal coproducts equal, produces goals mentioning
`(equalizerFork f g).pt.I` and these are type-correct only after the semireducible
`equalizerFork` is unfolded, so tactics working at `implicit` transparency (`rw`, and `exact
rfl` on the index component) are rejected. With the chosen `equalizer` the point of the fork
is rigid enough that the explicit `dsimp`/`change` steps below suffice.

The index universe `w` of the formal coproducts stays independent of the universes `u`, `v`
of `C`: the index type of the equalizer is a subtype of `X.I : Type w`, so nothing here
relates them.

## References

* [Stacks Project, Tag 01G2](https://stacks.math.columbia.edu/tag/01G2)
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits.FormalCoproduct

variable {C : Type u} [Category.{v} C] [HasEqualizers C]

section Equalizer

variable {X Y : FormalCoproduct.{w} C} (f g : X ⟶ Y)

/-- The fork of two morphisms `f g : X ⟶ Y` of formal coproducts whose index type is the
subtype of indices of `X` on which `f` and `g` agree and whose component over such an index
is the equalizer in `C` of the two component morphisms. -/
noncomputable def equalizerFork : Fork f g :=
  Fork.ofι
    (⟨fun i : {i : X.I // f.f i = g.f i} ↦ i.1, fun i ↦ equalizer.ι (f.φ i.1)
      (g.φ i.1 ≫ eqToHom (by rw [i.2]))⟩ :
      (⟨{i : X.I // f.f i = g.f i},
          fun i ↦ equalizer (f.φ i.1) (g.φ i.1 ≫ eqToHom (by rw [i.2]))⟩ :
        FormalCoproduct.{w} C) ⟶ X)
    (hom_ext (funext fun i ↦ i.2) fun i ↦ by
      rw [comp_eqToHom_iff]
      simpa [Category.assoc] using equalizer.condition (f.φ i.1)
        (g.φ i.1 ≫ eqToHom (by rw [i.2])))

/-- `equalizerFork f g` is an equalizer of `f` and `g`. -/
noncomputable def isLimitEqualizerFork : IsLimit (equalizerFork f g) := by
  refine Fork.IsLimit.mk (equalizerFork f g) (fun s ↦ ?_) ?_ ?_
  · exact ⟨fun i ↦ ⟨(Fork.ι s).f i, congrFun (congrArg Hom.f s.condition) i⟩,
      fun i ↦ equalizer.lift ((Fork.ι s).φ i) (by
        rw [← Category.assoc, ← comp_eqToHom_iff]
        simpa [Category.assoc] using ((hom_ext_iff _ _).1 s.condition).2 i)⟩
  · intro s
    dsimp [equalizerFork]
    refine hom_ext (funext fun i ↦ rfl) ?_
    intro i
    simp
  · intro s m hm
    refine hom_ext (funext fun i ↦ Subtype.ext (congrFun ((hom_ext_iff _ _).1 hm).1 i)) ?_
    intro i
    apply equalizer.hom_ext
    obtain ⟨h₁, h₂⟩ := (hom_ext_iff _ _).1 hm
    have hmf : (m.f i).1 = (Fork.ι s).f i := congrFun h₁ i
    have hmi : m.f i = ⟨(Fork.ι s).f i, congrFun (congrArg Hom.f s.condition) i⟩ :=
      Subtype.ext hmf
    have hz := eqToHom_naturality
      (fun k : {i : X.I // f.f i = g.f i} ↦
        equalizer.ι (f.φ k.1) (g.φ k.1 ≫ eqToHom (by rw [k.2]))) hmi
    have hh := h₂ i
    dsimp [category] at hh
    simpa [equalizerFork, category, hmf, Category.assoc, ← eqToHom_naturality, hz] using hh

end Equalizer

variable (C) in
/-- **Stacks Project, Tag 01G2**, equalizers clause. If `C` has equalizers, then so does its
category of formal coproducts — equivalently, the category `SR(C)` of semi-representable
objects of `C` has equalizers. -/
@[stacks 01G2 "equalizers", sga "4 V 7.3.0" "equalizers in SR(C)"]
instance instHasEqualizers : HasEqualizers (FormalCoproduct.{w} C) :=
  letI : ∀ {X Y : FormalCoproduct.{w} C} {f g : X ⟶ Y}, HasLimit (parallelPair f g) :=
    fun {_ _ f g} ↦ ⟨⟨⟨_, isLimitEqualizerFork f g⟩⟩⟩
  hasEqualizers_of_hasLimit_parallelPair (FormalCoproduct.{w} C)

end CategoryTheory.Limits.FormalCoproduct

end
