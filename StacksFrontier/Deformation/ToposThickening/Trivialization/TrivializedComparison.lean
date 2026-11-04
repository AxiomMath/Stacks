module

public import StacksFrontier.Deformation.ToposThickening.Trivialization.SplittingOf
public import StacksFrontier.Deformation.ToposThickening.Trivialization.TrivializedCategory
public import StacksFrontier.Deformation.ToposThickening.TrivializedThickeningComparison
import StacksCore.Tactic.StacksAttribute

/-!
# A trivialized thickening of ringed topoi, presented on the site of the thickening

A first order thickening `i : (Sh(C), O) ⟶ (Sh(D), O')` together with a trivialization is an
object of the category of trivialized first order thickenings of `(Sh(D), i_*O)`, which is the
ringed topos `(Sh(C), O)` read through the equivalence of underlying topoi that the thickening
provides. Conversely every object of that category *is* such a thickening with a
trivialization: a sheaf of commutative rings `A` with a surjection `π : A ⟶ O` whose kernel has
square zero and a chosen section `σ` of `π` presents the first order thickening

```
  (Sh(C), O) ⟶ (Sh(C), A)
```

whose underlying morphism of topoi is the identity of `Sh(C)` and whose structure map is `π`,
and `σ` is a trivialization of it. The two constructions identify the objects of the concrete
presentation `Deformation.ToposThickening.TrivializedThickening` with the first order
thickenings of ringed topoi carrying a trivialization, which is what makes
`Deformation.ToposThickening.TrivializedThickening.moduleEquivalence` the last clause of
Stacks 08MG about the objects the source speaks of.

## Main definitions

* `Deformation.ToposThickening.trivializedThickeningOfTrivialization`: the object of the
  category of trivialized first order thickenings attached to a thickening and a trivialization
  of it.
* `Deformation.ToposThickening.TrivializedThickening.toRingedToposHom`,
  `.firstOrderThickening` and `.trivialization`: the reverse construction — the morphism of
  ringed topoi presented by a trivialized thickening, its first order thickening structure and
  the trivialization its splitting provides.
* `Deformation.ToposThickening.TrivializedThickening.translateIso` and `.withSplitIso`:
  replacing the splitting of a trivialized thickening by another splitting of its surjection
  gives an isomorphic object, by translation along the difference of the two splittings.
* `Deformation.ToposThickening.TrivializedThickening.baseIsoFunctor` and
  `.baseIsoEquivalence`: trivialized thickenings over isomorphic base ring sheaves are the
  same.

## Main results

* `Deformation.ToposThickening.TrivializedThickening.trivializedThickeningOfTrivializationIso`:
  the reverse construction is a section of the forward one up to isomorphism — the trivialized
  thickening attached to the identity presentation of `T` and to the trivialization its
  splitting provides is `T` itself, read over the direct image of the base along the identity
  morphism of topoi.
* `Deformation.ToposThickening.TrivializedThickening.exists_thickening_trivialization_iso`:
  **Stacks 08MG**, clause (4) for the source's objects: every object of the category of
  trivialized first order thickenings of `(Sh(C), O)` comes from a first order thickening of
  ringed topoi with a trivialization.

## Implementation notes

The splitting of `trivializedThickeningOfTrivialization` is the one produced by
`Deformation.ToposThickening.splittingFromTrivialization`; its `SplitMono` structure, whose
retraction is the structure map of the thickening, is exactly the section condition required of
an object of the category. The square-zero condition is read off from the kernel description
and the square-zero law carried by the first order thickening.

The reverse construction presents the thickening on the site `C` of the base, with the identity
morphism of topoi underneath. This is what the source does when it says it will freely identify
the underlying topoi of a thickening, and nothing is lost by it: the direct image of a first
order thickening is an equivalence of topoi, so a thickening presented on any other site is
carried to one presented on `C`. What is *not* avoidable is the comparison
`Deformation.ToposThickening.pushforwardIdIso` of the direct image along the identity morphism
of topoi with the identity functor: the direct image transports the ring operations along `𝟭`,
so it is isomorphic but not equal to the identity, and the structure map of a morphism of
ringed topoi takes its values in the transported sheaf. That comparison is the identity on
underlying sheaves of sets, and `.baseIsoEquivalence` says that composing the surjection and
the splitting with an isomorphism of the base ring sheaf is an equivalence of categories, so
the round trip lands at `T` up to an isomorphism of categories and an isomorphism of objects.

The round trip is an isomorphism rather than an equality because the splitting the forward
construction produces is the one `splittingFromTrivialization` extracts from the retraction,
which is a section of the same surjection as `T.split` but is not presented as that section.
Two splittings of one surjection differ by a map into the square-zero kernel, and translation
along that difference is an automorphism of the structure sheaf over the base
(`.translateIso`), which is the isomorphism used. The structure sheaf and the surjection of the
round trip are `T`'s own, on the nose
(`.trivializedThickeningOfTrivialization_A`, `.trivializedThickeningOfTrivialization_proj`),
as are the square-zero ideal and its inclusion (`.firstOrderThickening_I`,
`.firstOrderThickening_incl_apply`) and the structure map of the retraction
(`.trivialization_retraction_fSharp`).

**What is identified is objects, not morphisms.** There is no category of morphisms of ringed
topoi in this development — `AlgebraicGeometry.RingedToposHom.comp` has no strict unit and
associativity laws, see the implementation notes of
`StacksFrontier/Deformation/ToposThickening/Trivialization/RingedToposId.lean` — so the source's
morphisms of trivialized thickenings (Stacks 08MK) cannot be assembled into a category to be
compared with the `Hom` of `Deformation.ToposThickening.TrivializedThickening`. What is proved
here is the correspondence of objects: the forward construction attaches an object of the
category to every first order thickening with a trivialization, and the reverse construction
exhibits every object of the category as such a thickening with a trivialization,
isomorphically. The two taken together make the forward construction surjective on isomorphism
classes of objects, which is what clause (4) needs of it.

The reverse construction asks of the site exactly what `AlgebraicGeometry.RingedToposHom` asks
of it: `J.HasSheafCompose (forget RingCat)` as well as
`J.HasSheafCompose (forget₂ CommRingCat RingCat)`.
`Deformation.ToposThickening.TrivializedThickening.moduleEquivalence` needs only the second,
because it never names a morphism of ringed topoi; the first is what it costs to speak of the
source's objects at all, and it is carried by every declaration in the `ToposThickening` family
that does.

## Universes

The reverse construction, like
`Deformation.ToposThickening.TrivializedThickening.moduleEquivalence`, is stated at a single
universe: a site `C : Type t` with `Category.{t} C` and sheaves valued in `Type t`, the setting
in which `Deformation.ToposThickening.TrivializedThickening` is declared. That is also what
forces `Y` in `trivializedThickeningOfTrivialization` to be a
`AlgebraicGeometry.RingedTopos.{t, t, t}` while `X` stays general. It is the source's own
setting, the Stacks Project fixing one universe throughout.

## References

* [Stacks Project, Tag 08MG](https://stacks.math.columbia.edu/tag/08MG)
* [Stacks Project, Tag 08MK](https://stacks.math.columbia.edu/tag/08MK) — what a morphism of
  trivialized first order thickenings is
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)
open Stacks.Sheaves.ToposPullback (pullbackCommRingSheafFunctorId)

universe v u w t

namespace Deformation.ToposThickening

section Forward

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{t, t, t}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{t})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]

/-- A trivialization of a first order thickening of ringed topoi exhibits the thickening as an
object of the category of trivialized first order thickenings of `(Sh(D), i_*O)`, which is the
ringed topos `(Sh(C), O)` read through the equivalence of underlying topoi. -/
@[stacks 08MG "a trivialized thickening is an object of the category; the target ringed topos \
is at a single universe, forced by Deformation.ToposThickening.TrivializedThickening, whose \
category is declared over a site C : Type u with Category.{u} C and sheaves valued in Type u — \
the source's own setting, since the Stacks Project fixes one universe throughout"]
noncomputable def trivializedThickeningOfTrivialization (i : RingedToposHom X Y)
    (hi : FirstOrderThickening i) (π : Trivialization i) :
    TrivializedThickening ((pushforwardCommRingFunctor i.toToposHom).obj X.O) where
  A := Y.O
  proj := i.fSharp
  split := ⟨(splittingFromTrivialization i hi π).1⟩
  split_proj := by
    obtain ⟨split, hs, _, hret⟩ := splittingFromTrivialization i hi π
    refine InducedCategory.hom_ext ?_
    change split ≫ i.fSharp.hom = 𝟙 _
    rw [← hret]
    exact hs.id
  sq_zero U x y hx hy := by
    obtain ⟨a, ha⟩ := (hi.kernel U x).mp hx
    obtain ⟨b, hb⟩ := (hi.kernel U y).mp hy
    rw [← ha, ← hb]
    exact hi.square_zero U a b

end Forward

variable {C : Type t} [Category.{t} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{t})]
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  {O : Sheaf J CommRingCat.{t}}

/-- The direct image of a sheaf of commutative rings along the identity morphism of topoi,
compared with the sheaf itself. -/
noncomputable abbrev pushforwardIdIso (P : Sheaf J CommRingCat.{t}) :
    (pushforwardCommRingFunctor (MorphismOfTopoi.id (Sheaf J (Type t)))).obj P ≅ P :=
  (pullbackCommRingSheafFunctorId J).app P

namespace TrivializedThickening

omit [J.HasSheafCompose (forget RingCat.{t})]
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- A section of the surjection of a trivialized thickening is a section on local sections. -/
theorem proj_section_apply (T : TrivializedThickening O) {s : O ⟶ T.A}
    (hs : s ≫ T.proj = 𝟙 O) (U : Cᵒᵖ) (a : O.obj.obj U) :
    (T.proj.hom.app U).hom ((s.hom.app U).hom a) = a := by
  simpa using congrArg (fun φ : O ⟶ O => (φ.hom.app U).hom a) hs

omit [J.HasSheafCompose (forget RingCat.{t})]
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- Multiplying a local section killed by the surjection by a local section of the structure
sheaf is multiplying it by the image under any splitting of the surjection: the difference of
the two factors is killed by the surjection, and the kernel has square zero. -/
theorem mul_eq_section_mul (T : TrivializedThickening O) {s : O ⟶ T.A}
    (hs : s ≫ T.proj = 𝟙 O) {U : Cᵒᵖ} (a x : T.A.obj.obj U)
    (hx : (T.proj.hom.app U).hom x = 0) :
    a * x = (s.hom.app U).hom ((T.proj.hom.app U).hom a) * x := by
  have h0 : (T.proj.hom.app U).hom (a - (s.hom.app U).hom ((T.proj.hom.app U).hom a)) = 0 := by
    rw [map_sub, T.proj_section_apply hs, sub_self]
  linear_combination T.sq_zero U _ x h0 hx

/-- Translation by the difference of two splittings of the surjection, on local sections. -/
noncomputable def translateEquiv (T : TrivializedThickening O) {s₁ s₂ : O ⟶ T.A}
    (h₁ : s₁ ≫ T.proj = 𝟙 O) (h₂ : s₂ ≫ T.proj = 𝟙 O) (U : Cᵒᵖ) :
    T.A.obj.obj U ≃+* T.A.obj.obj U where
  toFun a := a + ((s₂.hom.app U).hom ((T.proj.hom.app U).hom a) -
    (s₁.hom.app U).hom ((T.proj.hom.app U).hom a))
  invFun a := a + ((s₁.hom.app U).hom ((T.proj.hom.app U).hom a) -
    (s₂.hom.app U).hom ((T.proj.hom.app U).hom a))
  left_inv a := by
    have hp : (T.proj.hom.app U).hom (a + ((s₂.hom.app U).hom ((T.proj.hom.app U).hom a) -
        (s₁.hom.app U).hom ((T.proj.hom.app U).hom a))) = (T.proj.hom.app U).hom a := by
      rw [map_add, map_sub, T.proj_section_apply h₁, T.proj_section_apply h₂, sub_self, add_zero]
    change a + ((s₂.hom.app U).hom ((T.proj.hom.app U).hom a) -
        (s₁.hom.app U).hom ((T.proj.hom.app U).hom a)) +
      ((s₁.hom.app U).hom ((T.proj.hom.app U).hom (a +
          ((s₂.hom.app U).hom ((T.proj.hom.app U).hom a) -
            (s₁.hom.app U).hom ((T.proj.hom.app U).hom a)))) -
        (s₂.hom.app U).hom ((T.proj.hom.app U).hom (a +
          ((s₂.hom.app U).hom ((T.proj.hom.app U).hom a) -
            (s₁.hom.app U).hom ((T.proj.hom.app U).hom a))))) = a
    rw [hp]
    ring
  right_inv a := by
    have hp : (T.proj.hom.app U).hom (a + ((s₁.hom.app U).hom ((T.proj.hom.app U).hom a) -
        (s₂.hom.app U).hom ((T.proj.hom.app U).hom a))) = (T.proj.hom.app U).hom a := by
      rw [map_add, map_sub, T.proj_section_apply h₁, T.proj_section_apply h₂, sub_self, add_zero]
    change a + ((s₁.hom.app U).hom ((T.proj.hom.app U).hom a) -
        (s₂.hom.app U).hom ((T.proj.hom.app U).hom a)) +
      ((s₂.hom.app U).hom ((T.proj.hom.app U).hom (a +
          ((s₁.hom.app U).hom ((T.proj.hom.app U).hom a) -
            (s₂.hom.app U).hom ((T.proj.hom.app U).hom a)))) -
        (s₁.hom.app U).hom ((T.proj.hom.app U).hom (a +
          ((s₁.hom.app U).hom ((T.proj.hom.app U).hom a) -
            (s₂.hom.app U).hom ((T.proj.hom.app U).hom a))))) = a
    rw [hp]
    ring
  map_mul' a b := by
    have hkb : (T.proj.hom.app U).hom ((s₂.hom.app U).hom ((T.proj.hom.app U).hom b) -
        (s₁.hom.app U).hom ((T.proj.hom.app U).hom b)) = 0 := by
      rw [map_sub, T.proj_section_apply h₁, T.proj_section_apply h₂, sub_self]
    have hka : (T.proj.hom.app U).hom ((s₂.hom.app U).hom ((T.proj.hom.app U).hom a) -
        (s₁.hom.app U).hom ((T.proj.hom.app U).hom a)) = 0 := by
      rw [map_sub, T.proj_section_apply h₁, T.proj_section_apply h₂, sub_self]
    have hav := T.mul_eq_section_mul h₁ a _ hkb
    have hub := T.mul_eq_section_mul h₁ b _ hka
    change a * b + ((s₂.hom.app U).hom ((T.proj.hom.app U).hom (a * b)) -
        (s₁.hom.app U).hom ((T.proj.hom.app U).hom (a * b))) =
      (a + ((s₂.hom.app U).hom ((T.proj.hom.app U).hom a) -
          (s₁.hom.app U).hom ((T.proj.hom.app U).hom a))) *
        (b + ((s₂.hom.app U).hom ((T.proj.hom.app U).hom b) -
          (s₁.hom.app U).hom ((T.proj.hom.app U).hom b)))
    rw [map_mul, map_mul, map_mul]
    linear_combination - hav - hub
  map_add' a b := by
    show a + b + ((s₂.hom.app U).hom ((T.proj.hom.app U).hom (a + b)) -
        (s₁.hom.app U).hom ((T.proj.hom.app U).hom (a + b))) =
      (a + ((s₂.hom.app U).hom ((T.proj.hom.app U).hom a) -
          (s₁.hom.app U).hom ((T.proj.hom.app U).hom a))) +
        (b + ((s₂.hom.app U).hom ((T.proj.hom.app U).hom b) -
          (s₁.hom.app U).hom ((T.proj.hom.app U).hom b)))
    rw [map_add, map_add, map_add]
    ring

/-- Two splittings of the surjection of a trivialized thickening are carried into one another by
an automorphism of its structure sheaf over the base. -/
noncomputable def translateIso (T : TrivializedThickening O) {s₁ s₂ : O ⟶ T.A}
    (h₁ : s₁ ≫ T.proj = 𝟙 O) (h₂ : s₂ ≫ T.proj = 𝟙 O) : T.A ≅ T.A :=
  InducedCategory.isoMk (NatIso.ofComponents
    (fun U => (T.translateEquiv h₁ h₂ U).toCommRingCatIso) (by
      intro U V f
      refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
      have hs₁ : (T.A.obj.map f).hom ((s₁.hom.app U).hom ((T.proj.hom.app U).hom a)) =
          (s₁.hom.app V).hom ((O.obj.map f).hom ((T.proj.hom.app U).hom a)) :=
        (congrArg (fun g : O.obj.obj U ⟶ T.A.obj.obj V => g.hom ((T.proj.hom.app U).hom a))
          (s₁.hom.naturality f)).symm
      have hs₂ : (T.A.obj.map f).hom ((s₂.hom.app U).hom ((T.proj.hom.app U).hom a)) =
          (s₂.hom.app V).hom ((O.obj.map f).hom ((T.proj.hom.app U).hom a)) :=
        (congrArg (fun g : O.obj.obj U ⟶ T.A.obj.obj V => g.hom ((T.proj.hom.app U).hom a))
          (s₂.hom.naturality f)).symm
      change (T.A.obj.map f).hom a + ((s₂.hom.app V).hom
            ((T.proj.hom.app V).hom ((T.A.obj.map f).hom a)) -
          (s₁.hom.app V).hom ((T.proj.hom.app V).hom ((T.A.obj.map f).hom a))) =
        (T.A.obj.map f).hom (a + ((s₂.hom.app U).hom ((T.proj.hom.app U).hom a) -
          (s₁.hom.app U).hom ((T.proj.hom.app U).hom a)))
      rw [map_add, map_sub, hs₁, hs₂, T.proj_naturality_apply]))

omit [J.HasSheafCompose (forget RingCat.{t})]
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- The translation isomorphism adds to a local section the difference of the two splittings
applied to its image under the surjection. -/
@[simp]
theorem translateIso_hom_apply (T : TrivializedThickening O) {s₁ s₂ : O ⟶ T.A}
    (h₁ : s₁ ≫ T.proj = 𝟙 O) (h₂ : s₂ ≫ T.proj = 𝟙 O) (U : Cᵒᵖ) (a : T.A.obj.obj U) :
    ((T.translateIso h₁ h₂).hom.hom.app U).hom a =
      a + ((s₂.hom.app U).hom ((T.proj.hom.app U).hom a) -
        (s₁.hom.app U).hom ((T.proj.hom.app U).hom a)) := rfl

omit [J.HasSheafCompose (forget RingCat.{t})]
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- Translating the splittings does not change the surjection. -/
theorem translateIso_hom_comp_proj (T : TrivializedThickening O) {s₁ s₂ : O ⟶ T.A}
    (h₁ : s₁ ≫ T.proj = 𝟙 O) (h₂ : s₂ ≫ T.proj = 𝟙 O) :
    (T.translateIso h₁ h₂).hom ≫ T.proj = T.proj := by
  apply InducedCategory.hom_ext
  refine NatTrans.ext (funext fun U => CommRingCat.hom_ext (RingHom.ext fun a => ?_))
  change (T.proj.hom.app U).hom (a + ((s₂.hom.app U).hom ((T.proj.hom.app U).hom a) -
      (s₁.hom.app U).hom ((T.proj.hom.app U).hom a))) = (T.proj.hom.app U).hom a
  rw [map_add, map_sub, T.proj_section_apply h₁, T.proj_section_apply h₂, sub_self, add_zero]

omit [J.HasSheafCompose (forget RingCat.{t})]
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- Translating the splittings carries the first splitting to the second. -/
theorem comp_translateIso_hom (T : TrivializedThickening O) {s₁ s₂ : O ⟶ T.A}
    (h₁ : s₁ ≫ T.proj = 𝟙 O) (h₂ : s₂ ≫ T.proj = 𝟙 O) :
    s₁ ≫ (T.translateIso h₁ h₂).hom = s₂ := by
  apply InducedCategory.hom_ext
  refine NatTrans.ext (funext fun U => CommRingCat.hom_ext (RingHom.ext fun a => ?_))
  change (s₁.hom.app U).hom a + ((s₂.hom.app U).hom ((T.proj.hom.app U).hom
        ((s₁.hom.app U).hom a)) -
      (s₁.hom.app U).hom ((T.proj.hom.app U).hom ((s₁.hom.app U).hom a))) =
    (s₂.hom.app U).hom a
  rw [T.proj_section_apply h₁]
  ring

omit [J.HasSheafCompose (forget RingCat.{t})]
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- Translating a splitting into itself is the identity. -/
theorem translateIso_self (T : TrivializedThickening O) {s : O ⟶ T.A}
    (hs : s ≫ T.proj = 𝟙 O) : T.translateIso hs hs = Iso.refl T.A := by
  refine Iso.ext (InducedCategory.hom_ext (NatTrans.ext (funext fun U =>
    CommRingCat.hom_ext (RingHom.ext fun a => ?_))))
  change a + ((s.hom.app U).hom ((T.proj.hom.app U).hom a) -
    (s.hom.app U).hom ((T.proj.hom.app U).hom a)) = a
  rw [sub_self, add_zero]

/-- A trivialized thickening with its splitting replaced by another splitting of the same
surjection. -/
abbrev withSplit (T : TrivializedThickening O) {s : O ⟶ T.A} (hs : s ≫ T.proj = 𝟙 O) :
    TrivializedThickening O where
  A := T.A
  proj := T.proj
  split := s
  split_proj := hs
  sq_zero := T.sq_zero

/-- Replacing the splitting of a trivialized thickening by another splitting of its surjection
gives an isomorphic object, the isomorphism being translation by the difference of the two
splittings. -/
noncomputable def withSplitIso (T : TrivializedThickening O) {s : O ⟶ T.A}
    (hs : s ≫ T.proj = 𝟙 O) : T.withSplit hs ≅ T where
  hom := ⟨(T.translateIso hs T.split_proj).hom, T.translateIso_hom_comp_proj hs T.split_proj,
    T.comp_translateIso_hom hs T.split_proj⟩
  inv := ⟨(T.translateIso hs T.split_proj).inv,
    (Iso.inv_comp_eq _).mpr (T.translateIso_hom_comp_proj hs T.split_proj).symm,
    (Iso.comp_inv_eq _).mpr (T.comp_translateIso_hom hs T.split_proj).symm⟩
  hom_inv_id := hom_ext (T.translateIso hs T.split_proj).hom_inv_id
  inv_hom_id := hom_ext (T.translateIso hs T.split_proj).inv_hom_id

section BaseIso

variable {O' : Sheaf J CommRingCat.{t}}

omit [J.HasSheafCompose (forget RingCat.{t})]
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
private theorem inv_hom_app_apply {P Q : Sheaf J CommRingCat.{t}} (e : P ≅ Q) (U : Cᵒᵖ)
    (a : P.obj.obj U) : (e.inv.hom.app U).hom ((e.hom.hom.app U).hom a) = a := by
  have h : e.hom.hom.app U ≫ e.inv.hom.app U = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom, e.hom_inv_id]
    rfl
  exact ConcreteCategory.congr_hom h a

omit [J.HasSheafCompose (forget RingCat.{t})]
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
private theorem hom_inv_app_apply {P Q : Sheaf J CommRingCat.{t}} (e : P ≅ Q) (U : Cᵒᵖ)
    (b : Q.obj.obj U) : (e.hom.hom.app U).hom ((e.inv.hom.app U).hom b) = b :=
  inv_hom_app_apply e.symm U b

/-- Reading trivialized thickenings over an isomorphic base ring sheaf: the structure sheaf and
its kernel are unchanged, the surjection and the splitting are composed with the
isomorphism. -/
noncomputable def baseIsoFunctor (e : O ≅ O') :
    TrivializedThickening O ⥤ TrivializedThickening O' where
  obj T :=
    { A := T.A
      proj := T.proj ≫ e.hom
      split := e.inv ≫ T.split
      split_proj := by
        rw [Category.assoc, ← Category.assoc T.split, T.split_proj, Category.id_comp,
          e.inv_hom_id]
      sq_zero := fun U x y hx hy => T.sq_zero U x y
        (by
          have h : (e.inv.hom.app U).hom ((e.hom.hom.app U).hom
              ((T.proj.hom.app U).hom x)) = (e.inv.hom.app U).hom 0 := congrArg _ hx
          rw [inv_hom_app_apply e U, map_zero] at h
          exact h)
        (by
          have h : (e.inv.hom.app U).hom ((e.hom.hom.app U).hom
              ((T.proj.hom.app U).hom y)) = (e.inv.hom.app U).hom 0 := congrArg _ hy
          rw [inv_hom_app_apply e U, map_zero] at h
          exact h) }
  map f := ⟨f.hom, by rw [← Category.assoc, f.hom_proj], by rw [Category.assoc, f.split_hom]⟩
  map_id T := hom_ext rfl
  map_comp f g := hom_ext rfl

omit [J.HasSheafCompose (forget RingCat.{t})]
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- Reading a trivialized thickening over an isomorphic base keeps its structure sheaf. -/
@[simp]
theorem baseIsoFunctor_obj_A (e : O ≅ O') (T : TrivializedThickening O) :
    ((baseIsoFunctor e).obj T).A = T.A := rfl

omit [J.HasSheafCompose (forget RingCat.{t})]
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- Reading a trivialized thickening over an isomorphic base composes its surjection with the
isomorphism. -/
@[simp]
theorem baseIsoFunctor_obj_proj (e : O ≅ O') (T : TrivializedThickening O) :
    ((baseIsoFunctor e).obj T).proj = T.proj ≫ e.hom := rfl

omit [J.HasSheafCompose (forget RingCat.{t})]
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- Reading a trivialized thickening over an isomorphic base precomposes its splitting with the
inverse of the isomorphism. -/
@[simp]
theorem baseIsoFunctor_obj_split (e : O ≅ O') (T : TrivializedThickening O) :
    ((baseIsoFunctor e).obj T).split = e.inv ≫ T.split := rfl

omit [J.HasSheafCompose (forget RingCat.{t})]
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- Reading over an isomorphic base keeps the underlying morphism of structure sheaves. -/
@[simp]
theorem baseIsoFunctor_map_hom (e : O ≅ O') {T S : TrivializedThickening O} (f : T ⟶ S) :
    ((baseIsoFunctor e).map f).hom = f.hom := rfl

/-- **Trivialized thickenings over isomorphic base ring sheaves are the same.** The two
categories are equivalent, by composing the surjection and the splitting with the
isomorphism. -/
noncomputable def baseIsoEquivalence (e : O ≅ O') :
    TrivializedThickening O ≌ TrivializedThickening O' where
  functor := baseIsoFunctor e
  inverse := baseIsoFunctor e.symm
  unitIso := NatIso.ofComponents (fun T =>
    { hom := ⟨𝟙 T.A, by simp, by simp⟩
      inv := ⟨𝟙 T.A, by simp, by simp⟩
      hom_inv_id := hom_ext (Category.comp_id _)
      inv_hom_id := hom_ext (Category.comp_id _) })
    (fun f => hom_ext ((Category.comp_id _).trans (Category.id_comp _).symm))
  counitIso := NatIso.ofComponents (fun T =>
    { hom := ⟨𝟙 T.A, by simp, by simp⟩
      inv := ⟨𝟙 T.A, by simp, by simp⟩
      hom_inv_id := hom_ext (Category.comp_id _)
      inv_hom_id := hom_ext (Category.comp_id _) })
    (fun f => hom_ext ((Category.comp_id _).trans (Category.id_comp _).symm))
  functor_unitIso_comp T := hom_ext (Category.comp_id _)

end BaseIso

section Reverse

variable (T : TrivializedThickening O)

/-- **The identity presentation of a trivialized thickening**: the morphism of ringed topoi
`(Sh(C), O) ⟶ (Sh(C), A)` whose underlying morphism of topoi is the identity of `Sh(C)` and
whose structure map is the surjection of the trivialized thickening, read through the
comparison of the direct image along the identity morphism of topoi with the identity
functor. -/
noncomputable def toRingedToposHom :
    RingedToposHom (ringedToposOn J O) (ringedToposOn J T.A) :=
  homOn (MorphismOfTopoi.id (Sheaf J (Type t))) (T.proj ≫ (pushforwardIdIso O).inv)

/-- The underlying morphism of topoi of the identity presentation is the identity of `Sh(C)`. -/
@[simp]
theorem toRingedToposHom_toToposHom :
    T.toRingedToposHom.toToposHom = MorphismOfTopoi.id (Sheaf J (Type t)) := rfl

/-- The structure map of the identity presentation is the surjection, read through the
comparison of the direct image along the identity with the identity functor. -/
@[simp]
theorem toRingedToposHom_fSharp :
    T.toRingedToposHom.fSharp = T.proj ≫ (pushforwardIdIso O).inv := rfl

/-- The ideal of a trivialized thickening, read over the direct image of the base along the
identity morphism of topoi. -/
noncomputable abbrev idealOverPushforwardId :
    SheafOfModules.{t} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((pushforwardCommRingFunctor (MorphismOfTopoi.id (Sheaf J (Type t)))).obj O)) :=
  (SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat.{t} RingCat.{t})).map
      (pushforwardIdIso O).hom)).obj T.ideal

/-- The ideal of a trivialized thickening, read as a module over the structure sheaf of its
identity presentation. -/
noncomputable def idealOverStructureSheaf :
    SheafOfModules.{t} (Stacks.SheafOfModules.Tensor.ringSheaf T.A) :=
  (SheafOfModules.restrictScalars
    (show Stacks.SheafOfModules.Tensor.ringSheaf T.A ⟶ _ from
      (sheafCompose J (forget₂ CommRingCat.{t} RingCat.{t})).map
        T.toRingedToposHom.fSharp)).obj T.idealOverPushforwardId

/-- The inclusion of the ideal in the structure sheaf of the identity presentation. -/
noncomputable def idealInclusion :
    T.idealOverStructureSheaf ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf T.A) :=
  SheafOfModules.Hom.mk
    { app := fun U =>
        letI : Module ((Stacks.SheafOfModules.Tensor.ringSheaf T.A).obj.obj U)
            (T.idealOverPushforwardId.val.obj U) :=
          (T.idealOverStructureSheaf.val.obj U).isModule
        ModuleCat.ofHom
          { toFun := fun x => x.1
            map_add' := fun _ _ => rfl
            map_smul' := fun r x => by
              have h1 : ((pushforwardIdIso O).hom.hom.app U).hom
                  (((pushforwardIdIso O).inv.hom.app U).hom ((T.proj.hom.app U).hom r)) =
                  (T.proj.hom.app U).hom r := hom_inv_app_apply _ U _
              exact (congrArg (fun z => (T.split.hom.app U).hom z * x.1) h1).trans
                (T.mul_eq_section_mul T.split_proj r x.1 (T.mem_idealSections.mp x.2)).symm }
      naturality := fun _ => rfl }

/-- The identity presentation is a first order thickening. -/
noncomputable def firstOrderThickening : FirstOrderThickening T.toRingedToposHom where
  equiv := show (𝟭 (Sheaf J (Type t))).IsEquivalence from inferInstance
  surjective := Presheaf.isLocallySurjective_of_surjective J _ fun U y =>
    ⟨(T.split.hom.app U).hom (((pushforwardIdIso O).hom.hom.app U).hom y), by
      change ((pushforwardIdIso O).inv.hom.app U).hom ((T.proj.hom.app U).hom
        ((T.split.hom.app U).hom (((pushforwardIdIso O).hom.hom.app U).hom y))) = y
      rw [T.proj_split_apply]
      exact inv_hom_app_apply _ U y⟩
  I := T.idealOverPushforwardId
  incl := T.idealInclusion
  kernel := fun U a => by
    refine ⟨fun ha => ⟨⟨a, T.mem_idealSections.mpr ?_⟩, rfl⟩, ?_⟩
    · exact (hom_inv_app_apply _ U _).symm.trans
        ((congrArg ((pushforwardIdIso O).hom.hom.app U).hom ha).trans (map_zero _))
    · rintro ⟨b, rfl⟩
      change ((pushforwardIdIso O).inv.hom.app U).hom ((T.proj.hom.app U).hom b.1) = 0
      rw [T.mem_idealSections.mp b.2, map_zero]
  injective := fun _ _ _ h => Subtype.ext h
  square_zero := fun U a b => T.sq_zero U a.1 b.1 (T.mem_idealSections.mp a.2)
    (T.mem_idealSections.mp b.2)

/-- The splitting of a trivialized thickening is a trivialization of its identity
presentation. -/
noncomputable def trivialization : Trivialization T.toRingedToposHom where
  retraction := homOn (MorphismOfTopoi.id (Sheaf J (Type t)))
    (T.split ≫ (pushforwardIdIso T.A).inv)
  comp_id := by
    have hforget : ∀ P : Sheaf J CommRingCat.{t},
        (sheafCompose J (forget CommRingCat.{t})).map (pushforwardIdIso P).inv =
          𝟙 ((sheafCompose J (forget CommRingCat.{t})).obj P) := fun P =>
      (Iso.inv_eq_inv ((sheafCompose J (forget CommRingCat.{t})).mapIso (pushforwardIdIso P))
          (Iso.refl _)).mpr
        (Stacks.Sheaves.ToposPullback.forget_map_pullbackCommRingSheafFunctorId_hom_app J P)
    have happ : ∀ (P : Sheaf J CommRingCat.{t}) (U : Cᵒᵖ) (y : P.obj.obj U),
        ((pushforwardIdIso P).inv.hom.app U).hom y = y := fun P U y =>
      congrArg (fun m : (sheafCompose J (forget CommRingCat.{t})).obj P ⟶
        (sheafCompose J (forget CommRingCat.{t})).obj P => m.hom.app U y) (hforget P)
    refine ⟨Iso.refl _, ?_⟩
    rw [RingedToposHom.comp_fSharp_forget]
    apply InducedCategory.hom_ext
    ext U x
    change ((pushforwardIdIso O).inv.hom.app U).hom ((T.proj.hom.app U).hom
      (((pushforwardIdIso T.A).inv.hom.app U).hom ((T.split.hom.app U).hom x))) = x
    rw [happ T.A U, happ O U]
    exact T.proj_split_apply U x

/-- The structure map of the retraction of the trivialization is the splitting, read through the
comparison of the direct image along the identity with the identity functor. -/
@[simp]
theorem trivialization_retraction_fSharp :
    T.trivialization.retraction.fSharp = T.split ≫ (pushforwardIdIso T.A).inv := rfl

/-- The ideal of the identity presentation as a first order thickening is the ideal of the
trivialized thickening, read over the direct image of the base along the identity. -/
@[simp]
theorem firstOrderThickening_I : T.firstOrderThickening.I = T.idealOverPushforwardId := rfl

/-- The inclusion of the ideal of the identity presentation sends a local section of the ideal
to itself, as a local section of the structure sheaf. -/
theorem firstOrderThickening_incl_apply (U : Cᵒᵖ) (x : T.idealSections U) :
    (show T.A.obj.obj U from T.firstOrderThickening.incl.val.app U x) = x.1 := rfl

/-- The trivialized thickening attached to the identity presentation of `T` and its
trivialization has the structure sheaf of `T`. -/
@[simp]
theorem trivializedThickeningOfTrivialization_A :
    (trivializedThickeningOfTrivialization T.toRingedToposHom T.firstOrderThickening
      T.trivialization).A = T.A := rfl

/-- The trivialized thickening attached to the identity presentation of `T` and its
trivialization has the surjection of `T`, read over the direct image of the base along the
identity. -/
@[simp]
theorem trivializedThickeningOfTrivialization_proj :
    (trivializedThickeningOfTrivialization T.toRingedToposHom T.firstOrderThickening
      T.trivialization).proj = T.proj ≫ (pushforwardIdIso O).inv := rfl

/-- **The identity presentation recovers the trivialized thickening it was built from.** The
object attached to the identity presentation of `T` and to the trivialization its splitting
provides has `T`'s own structure sheaf and surjection, and is isomorphic to `T` read over the
direct image of the base along the identity morphism of topoi; the isomorphism is the
translation taking the splitting the forward construction extracts from the retraction to the
splitting of `T`. -/
noncomputable def trivializedThickeningOfTrivializationIso :
    trivializedThickeningOfTrivialization T.toRingedToposHom T.firstOrderThickening
        T.trivialization ≅ (baseIsoFunctor (pushforwardIdIso O).symm).obj T :=
  withSplitIso ((baseIsoFunctor (pushforwardIdIso O).symm).obj T)
    (trivializedThickeningOfTrivialization T.toRingedToposHom T.firstOrderThickening
      T.trivialization).split_proj

/-- **Stacks 08MG, clause (4), for the source's objects.** Every object of the category of
trivialized first order thickenings of `(Sh(C), O)` is, up to isomorphism, the trivialized
thickening of a first order thickening of ringed topoi `(Sh(C), O) ⟶ (Sh(C), A)` together with
a trivialization of it. With
`Deformation.ToposThickening.trivializedThickeningOfTrivialization` in the other direction this
identifies the objects of the two presentations, so that
`Deformation.ToposThickening.TrivializedThickening.moduleEquivalence` reads as the source's
sentence about the source's objects: the category of trivialized first order thickenings of
`(Sh(C), O)` is equivalent to the category of `O`-modules. -/
@[stacks 08MG "clause (4) for the source's objects: every object of the category of \
trivialized first order thickenings of (Sh(C), O) is the trivialized thickening of a first \
order thickening of ringed topoi (Sh(C), O) ⟶ (Sh(C), A) with a trivialization of it, up to \
the isomorphism of objects supplied here and the equivalence of categories \
Deformation.ToposThickening.TrivializedThickening.baseIsoEquivalence that reads the base \
through the comparison of the direct image along the identity morphism of topoi with the \
identity functor; together with \
Deformation.ToposThickening.trivializedThickeningOfTrivialization in the other direction this \
identifies the objects of the two presentations, which is what makes \
Deformation.ToposThickening.TrivializedThickening.moduleEquivalence the source's sentence \
about the source's objects; the thickening is presented on the site of the base, which loses \
nothing because the direct image of a first order thickening is an equivalence of topoi, and \
at a single universe, the Stacks Project's own convention"]
theorem exists_thickening_trivialization_iso :
    ∃ (hi : FirstOrderThickening T.toRingedToposHom) (π : Trivialization T.toRingedToposHom),
      Nonempty (trivializedThickeningOfTrivialization T.toRingedToposHom hi π ≅
        (baseIsoFunctor (pushforwardIdIso O).symm).obj T) :=
  ⟨T.firstOrderThickening, T.trivialization, ⟨T.trivializedThickeningOfTrivializationIso⟩⟩

end Reverse

end TrivializedThickening

end Deformation.ToposThickening

end
