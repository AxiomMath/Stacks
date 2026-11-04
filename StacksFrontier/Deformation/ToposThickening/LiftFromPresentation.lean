module

public import StacksFrontier.CategoryTheory.Sites.RingSheafDescent
public import StacksFrontier.CategoryTheory.Sites.RingSheafSections
public import StacksFrontier.Deformation.ToposThickening.SquareZeroTwist
public import StacksFrontier.Deformation.ToposThickening.FirstOrderLiftDiagram

/-!
# Step 3 of the proof of Stacks 08UG: a twisted presentation yields a lift

Step 3 of the proof of [Stacks Project, Tag 08UG] produces the missing comparison morphism
`𝒪'₁ ⟶ 𝒪'₂` of the source's diagram out of a factorization `θ` of the obstruction homomorphism
`ξ` through the degree `0` term of `NL(α)`. Its shape is: take the polynomial presentation
`a : 𝒪_{ℬ'₁}[ℰ] ⟶ 𝒪'₁` of Step 1 and the second algebra map `b : 𝒪_{ℬ'₁}[ℰ] ⟶ 𝒪'₂`, twist `b` by
the derivation `θ ∘ d`, observe that the twist agrees with `ν ∘ a` on the ideal of the
presentation, and descend along `a`.

This file carries out that shape, for an *arbitrary* presentation of the front thickened
structure sheaf rather than the polynomial one: given a locally surjective `a : ℛ ⟶ 𝒪'₁`, a
homomorphism `b : ℛ ⟶ 𝒪'₂`, a derivation `δ` of `ℛ` into `𝒢₂` along `b`, and the three
compatibilities the source checks for `b + θ ∘ d`, it builds a
`Deformation.ToposThickening.FirstOrderLiftDiagram.Lift`. What remains of Step 3 after this is the
identification of `(ℛ, a, b, δ)` with the polynomial presentation of Step 1 and the verification
of the three compatibilities from the pinning of `ξ` — see the implementation notes.

## Main definitions

* `Deformation.ToposThickening.FirstOrderLiftDiagram.liftOfTwist`: the lift of the diagram built
  from such a presentation.

## Main results

* `Deformation.ToposThickening.FirstOrderLiftDiagram.liftOfTwist_comp`: the lift restricts along
  the presentation to the twisted homomorphism, which is what pins it down.
* `Deformation.ToposThickening.FirstOrderLiftDiagram.nonempty_lift_of_twist`: the conclusion of
  Step 3 in the form clause (1) consumes it — such a presentation makes the lifts of the
  diagram nonempty.

## Implementation notes

The three compatibilities are exactly the three clauses of
`Deformation.ToposThickening.FirstOrderLiftDiagram.Lift`, pulled back along the presentation, and
each is checked at the only place where it can be:

* `reduction_comm` is an identity of morphisms out of `𝒪'₁`, so it is obtained by cancelling the
  locally surjective `a` on the left
  (`Stacks.Sites.RingDescent.hom_ext_of_isLocallySurjective`) against the hypothesis `hred`;
  twisting does not disturb it, by
  `Deformation.ToposThickening.LiftSquare.twist_comp_reduction`.
* `base_comm` needs no cancellation: the hypothesis `hc` factors the structure map
  `𝒪_{ℬ'₁} ⟶ 𝒪'₁` of the front layer through the presentation — in the source's situation it is
  the coefficient map of the polynomial algebra — so the clause becomes the hypothesis `hbase`
  directly.
* `kernel_comm` is a *sectionwise* identity which the presentation only sees locally: a section
  of the ideal of the front layer is the image of a section of `ℛ` merely on a covering sieve,
  since `a` is only locally surjective. Both sides are therefore compared on the image sieve of
  `a` and the identity is concluded from separatedness of `𝒪'₂`,
  `Stacks.Sites.RingSections.section_eq_of_locally_eq`. This is the one clause for which the
  universe-unrestricted sheaf condition on sections is needed; Mathlib's
  `CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget` would have forced the ring universe to be
  the join of the site's two, which is not the setting a `FirstOrderLiftDiagram` carrying a
  polynomial presentation lives in.

The hypothesis of the descent itself — that the twist annihilates the kernel of `a` — is *not*
a separate assumption: it is the hypothesis `hideal` at the zero section of the ideal, since
`ν` is additive.

**What is still owed for Step 3, and hence for clause (1).** The data `(ℛ, a, b, δ)` and the
three compatibilities, for the source's own presentation. Concretely, with
`ℰ = 𝒪'₁ ×_{𝒪₂} 𝒪'₂` and `ℛ = 𝒪_{ℬ'₁}[ℰ]`:

* `a` and `b` are the two algebra maps of Step 1 and `hc` is the coefficient map of `ℛ`; local
  surjectivity of `a` holds because `a` is the first projection of `ℰ` on the variables.
* `δ` is `θ ∘ d` for a factorization `θ` of `ξ`, which is an
  `Deformation.ToposThickening.SectionwiseDerivation` of the back layer along `b` because
  the degree `0` term of `NL(α)` is a module over the *reduced* structure sheaf and `d` is a
  derivation.
* `hred` and `hbase` are read off the construction of `a` and `b`.
* `hideal` is the content of the factorization: on the ideal `ℐ'` of the presentation the twist
  `b + θ ∘ d` takes the value `ν ∘ a`, because `θ ∘ d|_{ℐ'} = ν ∘ a|_{ℐ'} - b|_{ℐ'}` is what
  `d ≫ θ = ξ` says once `ξ` is pinned as the difference of the two restrictions.

All of that (Steps 1 and 2 of 08UG/08U8) is not done in this file; this file is stated in the
vocabulary and universe setting of those steps so as to compose with them without change.

## References

* [Stacks Project, Tag 08UG](https://stacks.math.columbia.edu/tag/08UG)
* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u w

namespace Deformation.ToposThickening.FirstOrderLiftDiagram

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify J CommRingCat.{w}] [J.WEqualsLocallyBijective CommRingCat.{w}]
  [J.HasSheafCompose (forget CommRingCat.{w})]
  (D : FirstOrderLiftDiagram J) {R : Sheaf J CommRingCat.{w}} (a : R ⟶ D.front.O')
  [Presheaf.IsLocallySurjective J a.hom] (b : R ⟶ D.back.O')
  (δ : SectionwiseDerivation R D.back.G (b ≫ D.back.reduction)) (c : D.front.OB' ⟶ R)

omit [HasWeakSheafify J CommRingCat] [J.WEqualsLocallyBijective CommRingCat]
  [J.HasSheafCompose (forget CommRingCat)] in
/-- The comparison of the two ideal modules kills the zero section. -/
public theorem nuSection_zero (U : Cᵒᵖ) :
    D.nuSection (0 : D.front.G.val.obj U) = 0 :=
  map_zero (D.nu.val.app U).hom

omit [HasWeakSheafify J CommRingCat] [J.WEqualsLocallyBijective CommRingCat]
  [J.HasSheafCompose (forget CommRingCat)] in
/-- The comparison of the two ideal modules commutes with the restriction maps of the site. -/
public theorem nuSection_naturality {U V : Cᵒᵖ} (h : U ⟶ V) (m : D.front.G.val.obj U) :
    D.nuSection (show D.front.G.val.obj V from D.front.G.val.map h m) =
      show D.back.G.val.obj V from D.back.G.val.map h (D.nuSection m) :=
  PresheafOfModules.naturality_apply D.nu.val h m

variable
  (hideal : ∀ (U : Cᵒᵖ) (m : D.front.G.val.obj U) (x : R.obj.obj U),
    a.hom.app U x = D.front.incl m →
      (D.back.twist b δ).hom.app U x = D.back.incl (D.nuSection m))

omit [HasWeakSheafify J CommRingCat] [J.WEqualsLocallyBijective CommRingCat]
  [J.HasSheafCompose (forget CommRingCat)] [Presheaf.IsLocallySurjective J a.hom] in
include hideal in
/-- **The twist annihilates the kernel of the presentation**, so it descends along it. This is
the hypothesis `hideal` at the zero section of the ideal of the front layer. -/
public theorem twist_eq_zero_of_apply_eq_zero (U : Cᵒᵖ) (x : R.obj.obj U)
    (hx : a.hom.app U x = 0) : (D.back.twist b δ).hom.app U x = 0 := by
  have h0 : a.hom.app U x = D.front.incl (0 : D.front.G.val.obj U) := by
    rw [D.front.incl_zero]
    exact hx
  rw [hideal U 0 x h0, D.nuSection_zero, D.back.incl_zero]

include hideal in
/-- The homomorphism `𝒪'₁ ⟶ 𝒪'₂` obtained by descending the twist along the presentation. -/
public noncomputable def descTwist : D.front.O' ⟶ D.back.O' :=
  Stacks.Sites.RingDescent.desc a (D.back.twist b δ)
    (D.twist_eq_zero_of_apply_eq_zero a b δ hideal)

/-- The descended homomorphism restricts along the presentation to the twist. -/
public theorem comp_descTwist :
    a ≫ D.descTwist a b δ hideal = D.back.twist b δ :=
  Stacks.Sites.RingDescent.comp_desc a (D.back.twist b δ)
    (D.twist_eq_zero_of_apply_eq_zero a b δ hideal)

/-- The descended homomorphism, on sections of the presentation. -/
public theorem descTwist_apply (U : Cᵒᵖ) (x : R.obj.obj U) :
    (D.descTwist a b δ hideal).hom.app U (a.hom.app U x) =
      (D.back.twist b δ).hom.app U x :=
  congrArg (fun k : R ⟶ D.back.O' => k.hom.app U x) (D.comp_descTwist a b δ hideal)

include hideal in
/-- **Step 3 of the proof of [Stacks Project, Tag 08UG]**, for an arbitrary presentation of the
front thickened structure sheaf. A locally surjective `a : ℛ ⟶ 𝒪'₁`, a homomorphism
`b : ℛ ⟶ 𝒪'₂`, a derivation `δ` of `ℛ` into `𝒢₂` along `b`, and the three compatibilities the
source checks for `b + θ ∘ d` produce a morphism fitting into the source's diagram compatibly
with `ν`.

The implementation notes of this file say what remains to instantiate this at the source's own
polynomial presentation, and where that material lives. -/
public noncomputable def liftOfTwist
    (hc : c ≫ a = D.front.f')
    (hred : ∀ (U : Cᵒᵖ) (x : R.obj.obj U),
      D.back.reduction.hom.app U (b.hom.app U x) =
        D.g.hom.app U (D.front.reduction.hom.app U (a.hom.app U x)))
    (hbase : ∀ (U : Cᵒᵖ) (t : D.front.OB'.obj.obj U),
      (D.back.twist b δ).hom.app U (c.hom.app U t) =
        D.back.f'.hom.app U (D.gB'.hom.app U t)) :
    D.Lift where
  hom := D.descTwist a b δ hideal
  reduction_app := fun U' x' => congrArg (fun k => k.hom.app U' x') (show
      D.descTwist a b δ hideal ≫ D.back.reduction = D.front.reduction ≫ D.g by
    refine Stacks.Sites.RingDescent.hom_ext_of_isLocallySurjective a ?_
    refine sheafHom_ext J fun U x => ?_
    change D.back.reduction.hom.app U
        ((D.descTwist a b δ hideal).hom.app U (a.hom.app U x)) =
      D.g.hom.app U (D.front.reduction.hom.app U (a.hom.app U x))
    rw [D.descTwist_apply a b δ hideal, LiftSquare.twist_apply, map_add,
      D.back.reduction_incl, add_zero]
    exact hred U x)
  base_app := fun U t => by
    rw [show D.front.f'.hom.app U t = a.hom.app U (c.hom.app U t) from
      (congrArg (fun k : D.front.OB' ⟶ D.front.O' => k.hom.app U t) hc).symm,
      D.descTwist_apply a b δ hideal]
    exact hbase U t
  kernel_comm := fun U m => by
    refine Stacks.Sites.RingSections.section_eq_of_locally_eq J D.back.O'.property
      (X := U.unop) (S := Presheaf.imageSieve a.hom (D.front.incl m))
      (Presheaf.imageSieve_mem J a.hom _) ?_
    rintro Y f ⟨x, hx⟩
    set m' : D.front.G.val.obj (op Y) := D.front.G.val.map f.op m with hm'
    calc D.back.O'.obj.map f.op
          ((D.descTwist a b δ hideal).hom.app U (D.front.incl m))
        = (D.descTwist a b δ hideal).hom.app (op Y)
            (D.front.O'.obj.map f.op (D.front.incl m)) :=
          (sheafHom_naturality_apply J (D.descTwist a b δ hideal) f.op _).symm
      _ = (D.descTwist a b δ hideal).hom.app (op Y) (a.hom.app (op Y) x) := by
          rw [← hx]
      _ = (D.back.twist b δ).hom.app (op Y) x := D.descTwist_apply a b δ hideal _ x
      _ = D.back.incl (D.nuSection m') := hideal (op Y) m' x (by
          rw [hm', D.front.incl_naturality f.op m]
          exact hx)
      _ = D.back.O'.obj.map f.op (D.back.incl (D.nuSection m)) := by
          rw [hm', D.nuSection_naturality f.op m, D.back.incl_naturality f.op]

/-- The lift built by `liftOfTwist` restricts along the presentation to the twist. -/
public theorem liftOfTwist_comp
    (hc : c ≫ a = D.front.f')
    (hred : ∀ (U : Cᵒᵖ) (x : R.obj.obj U),
      D.back.reduction.hom.app U (b.hom.app U x) =
        D.g.hom.app U (D.front.reduction.hom.app U (a.hom.app U x)))
    (hbase : ∀ (U : Cᵒᵖ) (t : D.front.OB'.obj.obj U),
      (D.back.twist b δ).hom.app U (c.hom.app U t) =
        D.back.f'.hom.app U (D.gB'.hom.app U t)) :
    a ≫ (D.liftOfTwist a b δ c hideal hc hred hbase).hom = D.back.twist b δ :=
  D.comp_descTwist a b δ hideal

include hideal in
/-- **The conclusion of Step 3 in the form clause (1) of [Stacks Project, Tag 08UG] consumes
it:** such a presentation makes the morphisms fitting into the source's diagram nonempty. -/
public theorem nonempty_lift_of_twist
    (hc : c ≫ a = D.front.f')
    (hred : ∀ (U : Cᵒᵖ) (x : R.obj.obj U),
      D.back.reduction.hom.app U (b.hom.app U x) =
        D.g.hom.app U (D.front.reduction.hom.app U (a.hom.app U x)))
    (hbase : ∀ (U : Cᵒᵖ) (t : D.front.OB'.obj.obj U),
      (D.back.twist b δ).hom.app U (c.hom.app U t) =
        D.back.f'.hom.app U (D.gB'.hom.app U t)) :
    Nonempty D.Lift :=
  ⟨D.liftOfTwist a b δ c hideal hc hred hbase⟩

end Deformation.ToposThickening.FirstOrderLiftDiagram

end
