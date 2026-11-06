module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.FreeTransitiveAction
public import StacksFrontier.Deformation.SchlessingerConditions.CofiberedLifts

/-!
# Infinitesimal automorphisms under a morphism over the base

Let `φ : 𝓐 → 𝓑` be a morphism of categories cofibered in groupoids over a common base `C`.
Applying `φ` to an automorphism of the source of a lifting arrow is a homomorphism
`Inf(x'/x) → Inf(φ(x')/φ(x))` of relative infinitesimal automorphism groups. It is compatible
with the two constructions of [Stacks, Tag 06JY].

The first compatibility is with pushforward of automorphisms: `φ` of a pushforward along a
lifting arrow is the pushforward along the image arrow.

The second is with the identification of [Stacks, Tag 06JI] across a fibre square: for a fibre
square `z = x₁ ×_x x₂` lying over a fibre square of the base, pushforward along the second
projection identifies the automorphisms of `z` trivial on the first projection with
`Inf(x₂/x)`, and that identification commutes with `φ`. Since both identifications are
bijections, surjectivity of `φ` on the one group is equivalent to surjectivity on the other.

Over a *thin* fibre every automorphism is relatively infinitesimal, so that over such a fibre
the relative statement is a statement about full automorphism groups. For a fibre square over a
thin fibre, `φ` is surjective on automorphisms of the square as soon as it is surjective on
automorphisms of the two factors.

## Main definitions

* `Deformation.fiberObj`: the image of an object of a fibre under a morphism over the base.
* `Deformation.mapFiberAut`: the induced homomorphism of fibre automorphism groups.
* `Deformation.mapRelativeInfinitesimalAutomorphisms`: the homomorphism of relative
  infinitesimal automorphism groups along a lifting arrow induced by a morphism over the base.

## Main results

* `Deformation.isHomLift_basedFunctor_map`: a morphism over the base takes a lifting arrow to
  a lifting arrow over the same arrow of the base.
* `Deformation.mapFiberAut_pushforwardAutomorphism`: a morphism over the base commutes with
  pushforward of automorphisms.
* `Deformation.relativeInfinitesimalAutomorphisms_eq_top_of_isThin`: over a thin fibre every
  automorphism is relatively infinitesimal.
* `Deformation.isPullback_map_of_isHomLift`: a square of lifting arrows over a fibre square of
  the base has that fibre square as its image.
* `Deformation.surjective_mapRelativeInfinitesimalAutomorphisms_of_surjective_mapFiberAut`,
  `Deformation.surjective_mapFiberAut_of_surjective_mapRelativeInfinitesimalAutomorphisms`:
  over a thin fibre the relative statement and the statement about automorphism groups agree.
* `Deformation.pushforwardEndomorphism_eq_conj`: pushforward along a split arrow is
  conjugation.
* `Deformation.surjective_mapFiberAut_of_isoOver`,
  `Deformation.surjective_mapFiberAut_of_pushforward`: surjectivity on automorphism groups is
  invariant under isomorphism over an isomorphism of base objects.
* `Deformation.mapRelativeInfinitesimalAutomorphisms_fibreSquareHom`: the naturality of the
  identification of [Stacks, Tag 06JI] across a fibre square.
* `Deformation.surjective_mapRelativeInfinitesimalAutomorphisms_fibreSquare_iff`: the
  resulting equivalence of the two surjectivity statements.
* `Deformation.surjective_mapFiberAut_of_fibreSquare`: for a fibre square over a thin fibre,
  surjectivity on the automorphisms of the two factors gives surjectivity on the automorphisms
  of the square.

## Implementation notes

Everything is stated over an arbitrary base category, and thinness of a fibre is the hypothesis
rather than the predeformation condition of [Stacks, Tag 06GS].

The image of an object of a fibre is `Deformation.fiberObj`, the pair of the image object with
the equality of its base, rather than the value of `Deformation.fiberFunctor`. The two agree only
up to unfolding a definition, which is not available at the transparency at which instances are
synthesized: an arrow of `𝓑` written as an arrow out of `(fiberFunctor φ R).obj x` does not have
the shape at which the `IsHomLift` instances for pushforwards are stated.
`Deformation.fiberObj` carries `instance_reducible` so that they are found.

## References

* [Stacks Project, Tag 06JI](https://stacks.math.columbia.edu/tag/06JI)
* [Stacks Project, Tag 06JP](https://stacks.math.columbia.edu/tag/06JP)
* [Stacks Project, Tag 06JY](https://stacks.math.columbia.edu/tag/06JY)
-/

@[expose] public section

namespace Deformation

open CategoryTheory CategoryTheory.Limits

universe uC vC uA vA uB vB u₁ v₁

/-! ### Automorphisms over a thin fibre, and pushforward along a split arrow -/

section Elementary

variable {F : Type u₁} [Category.{v₁} F] {C : Type uC} [Category.{vC} C] {p : F ⥤ C}

/-- Over a thin fibre every automorphism of the source of a lifting arrow is relatively
infinitesimal along it. -/
private theorem mem_relativeInfinitesimalAutomorphisms_of_isThin
    (hp : IsCofiberedInGroupoids p) {R S : C} (f : R ⟶ S) {x' : p.Fiber R} {x : p.Fiber S}
    (r : x'.1 ⟶ x.1) (hr : p.IsHomLift f r) (hthin : Quiver.IsThin (p.Fiber S))
    (a : Aut x') : a ∈ relativeInfinitesimalAutomorphisms hp f r hr := by
  have hsub := hthin x x
  exact MonoidHom.mem_ker.2 (Aut.ext (Subsingleton.elim _ _))

/-- **Over a thin fibre every automorphism is relatively infinitesimal.** If the target of a
lifting arrow lies in a thin fibre, every automorphism of its source is relatively
infinitesimal along it. -/
public theorem relativeInfinitesimalAutomorphisms_eq_top_of_isThin
    (hp : IsCofiberedInGroupoids p) {R S : C} (f : R ⟶ S) {x' : p.Fiber R} {x : p.Fiber S}
    (r : x'.1 ⟶ x.1) (hr : p.IsHomLift f r) (hthin : Quiver.IsThin (p.Fiber S)) :
    relativeInfinitesimalAutomorphisms hp f r hr = ⊤ :=
  (Subgroup.eq_top_iff' _).2 (mem_relativeInfinitesimalAutomorphisms_of_isThin hp f r hr hthin)

/-- **Verticality depends only on the base object.** Lying over the identity of a base object
is unchanged when that object is replaced by an equal one. -/
public theorem isHomLift_id_of_base_eq {A A' : C} (h : A = A') {a b : F} (f : a ⟶ b)
    (hf : p.IsHomLift (𝟙 A) f) : p.IsHomLift (𝟙 A') f :=
  h ▸ hf

/-- **A square of lifting arrows over a fibre square of the base has image that fibre
square**, up to the canonical identifications of the bases. -/
public theorem isPullback_map_of_isHomLift
    {D A₁ A₂ A : C} {π₁ : D ⟶ A₁} {π₂ : D ⟶ A₂} {g₁ : A₁ ⟶ A} {g₂ : A₂ ⟶ A}
    {z : p.Fiber D} {x₁ : p.Fiber A₁} {x₂ : p.Fiber A₂} {x : p.Fiber A}
    {c₁ : z.1 ⟶ x₁.1} {c₂ : z.1 ⟶ x₂.1} {f₁ : x₁.1 ⟶ x.1} {f₂ : x₂.1 ⟶ x.1}
    (hc₁ : p.IsHomLift π₁ c₁) (hc₂ : p.IsHomLift π₂ c₂)
    (hf₁ : p.IsHomLift g₁ f₁) (hf₂ : p.IsHomLift g₂ f₂)
    (hbase : IsPullback π₁ π₂ g₁ g₂) :
    IsPullback (p.map c₁) (p.map c₂) (p.map f₁) (p.map f₂) := by
  have := hc₁
  have := hc₂
  have := hf₁
  have := hf₂
  refine hbase.of_iso (eqToIso z.2.symm) (eqToIso x₁.2.symm) (eqToIso x₂.2.symm)
    (eqToIso x.2.symm) ?_ ?_ ?_ ?_
  · rw [IsHomLift.fac' p π₁ c₁]; simp
  · rw [IsHomLift.fac' p π₂ c₂]; simp
  · rw [IsHomLift.fac' p g₁ f₁]; simp
  · rw [IsHomLift.fac' p g₂ f₂]; simp

/-- **Pushforward along a split arrow is conjugation.** If `v` is a left inverse of a lifting
arrow `u`, the pushforward of an automorphism along `u` is its conjugate. -/
public theorem pushforwardEndomorphism_eq_conj (hp : IsCofiberedInGroupoids p)
    {R R' : C} {y : p.Fiber R} {y' : p.Fiber R'} (g : R ⟶ R') (u : y.1 ⟶ y'.1)
    (hu : p.IsHomLift g u) (v : y'.1 ⟶ y.1) (hvu : v ≫ u = 𝟙 y'.1) (a : Aut y) :
    pushforwardEndomorphism hp g u hu a = v ≫ a.asIso.hom.val ≫ u := by
  rw [hom_comp_eq_comp_pushforwardEndomorphism hp g u hu a, ← Category.assoc, hvu,
    Category.id_comp]

/-- **Pushforward along an isomorphism is invertible.** Pushing an automorphism forward along
the inverse of an isomorphism of lifting data and back recovers it. -/
public theorem pushforwardAutomorphism_pushforwardAutomorphism_inv
    (hp : IsCofiberedInGroupoids p)
    {R R' : C} {y : p.Fiber R} {y' : p.Fiber R'} {e : R ≅ R'} (u : y.1 ≅ y'.1)
    (hu : p.IsHomLift e.hom u.hom) (hui : p.IsHomLift e.inv u.inv) (b : Aut y') :
    pushforwardAutomorphism hp e.hom u.hom hu
        (pushforwardAutomorphism hp e.inv u.inv hui b) = b := by
  apply Aut.ext
  apply Iso.ext
  apply Functor.Fiber.hom_ext
  show pushforwardEndomorphism hp e.hom u.hom hu
    (pushforwardAutomorphism hp e.inv u.inv hui b) = b.asIso.hom.val
  rw [pushforwardEndomorphism_eq_conj hp e.hom u.hom hu u.inv u.inv_hom_id]
  show u.inv ≫ pushforwardEndomorphism hp e.inv u.inv hui b ≫ u.hom = b.asIso.hom.val
  rw [pushforwardEndomorphism_eq_conj hp e.inv u.inv hui u.hom u.hom_inv_id]
  simp

end Elementary

/-! ### The induced homomorphism of relative infinitesimal automorphisms -/

section Map

variable {C : Type uC} [Category.{vC} C] {𝓐 : BasedCategory.{vA, uA} C}
  {𝓑 : BasedCategory.{vB, uB} C}

/-- A morphism over the base takes a lifting arrow to a lifting arrow over the same arrow of
the base. -/
public theorem isHomLift_basedFunctor_map (φ : BasedFunctor 𝓐 𝓑) {R S : C} (f : R ⟶ S)
    {x y : 𝓐.obj} (g : x ⟶ y) (hg : 𝓐.p.IsHomLift f g) : 𝓑.p.IsHomLift f (φ.map g) :=
  let := hg
  φ.preserves_isHomLift f g

/-- The image of an object of a fibre under a morphism over the base: the image object,
together with the equality of its base. -/
@[instance_reducible]
public def fiberObj (φ : BasedFunctor 𝓐 𝓑) {R : C} (x : 𝓐.p.Fiber R) : 𝓑.p.Fiber R :=
  ⟨φ.obj x.1, (φ.w_obj x.1).trans x.2⟩

/-- The underlying object of the image of an object of a fibre. -/
public theorem fiberObj_coe (φ : BasedFunctor 𝓐 𝓑) {R : C} (x : 𝓐.p.Fiber R) :
    (fiberObj φ x).1 = φ.obj x.1 := rfl

/-- The homomorphism of fibre automorphism groups induced by a morphism over the base. -/
@[instance_reducible]
public noncomputable def mapFiberAut (φ : BasedFunctor 𝓐 𝓑) {R : C} (x : 𝓐.p.Fiber R) :
    Aut x →* Aut (fiberObj φ x) where
  toFun a := Aut.of
    { hom := ⟨φ.map a.asIso.hom.val,
        isHomLift_basedFunctor_map φ (𝟙 R) a.asIso.hom.val a.asIso.hom.2⟩
      inv := ⟨φ.map a.asIso.inv.val,
        isHomLift_basedFunctor_map φ (𝟙 R) a.asIso.inv.val a.asIso.inv.2⟩
      hom_inv_id := Functor.Fiber.hom_ext (by
        change φ.map a.asIso.hom.val ≫ φ.map a.asIso.inv.val = 𝟙 (φ.obj x.1)
        rw [← φ.toFunctor.map_comp,
          show a.asIso.hom.val ≫ a.asIso.inv.val = 𝟙 x.1 from
            congrArg Subtype.val a.asIso.hom_inv_id,
          φ.toFunctor.map_id])
      inv_hom_id := Functor.Fiber.hom_ext (by
        change φ.map a.asIso.inv.val ≫ φ.map a.asIso.hom.val = 𝟙 (φ.obj x.1)
        rw [← φ.toFunctor.map_comp,
          show a.asIso.inv.val ≫ a.asIso.hom.val = 𝟙 x.1 from
            congrArg Subtype.val a.asIso.inv_hom_id,
          φ.toFunctor.map_id]) }
  map_one' := Aut.ext (Iso.ext <| Functor.Fiber.hom_ext (by
    change φ.map (𝟙 x.1) = 𝟙 (φ.obj x.1)
    exact φ.toFunctor.map_id x.1))
  map_mul' a b := Aut.ext (Iso.ext <| Functor.Fiber.hom_ext (by
    change φ.map (b.asIso.hom.val ≫ a.asIso.hom.val) =
      φ.map b.asIso.hom.val ≫ φ.map a.asIso.hom.val
    exact φ.toFunctor.map_comp _ _))

/-- The underlying arrow of the image of a fibre automorphism is the image of its underlying
arrow. -/
public theorem mapFiberAut_hom_val (φ : BasedFunctor 𝓐 𝓑) {R : C} (x : 𝓐.p.Fiber R)
    (a : Aut x) : ((mapFiberAut φ x) a).asIso.hom.val = φ.map a.asIso.hom.val := rfl

/-- **The naturality of pushforward.** A morphism over the base carries the pushforward of an
automorphism along a lifting arrow to the pushforward along the image arrow. -/
public theorem mapFiberAut_pushforwardAutomorphism (φ : BasedFunctor 𝓐 𝓑)
    (hA : IsCofiberedInGroupoids 𝓐.p) (hB : IsCofiberedInGroupoids 𝓑.p)
    {R S : C} (f : R ⟶ S) {x' : 𝓐.p.Fiber R} {x : 𝓐.p.Fiber S}
    (r : x'.1 ⟶ x.1) (hr : 𝓐.p.IsHomLift f r) (a : Aut x') :
    (mapFiberAut φ x) (pushforwardAutomorphism hA f r hr a) =
      pushforwardAutomorphism (x' := fiberObj φ x') (x := fiberObj φ x) hB f (φ.map r)
        (isHomLift_basedFunctor_map φ f r hr) ((mapFiberAut φ x') a) := by
  have hrB := isHomLift_basedFunctor_map φ f r hr
  have := hrB
  have := isStronglyCocartesian_of_isCofiberedInGroupoids (a := (fiberObj φ x').1)
    (b := (fiberObj φ x).1) hB f (φ.map r) hrB
  have hleft : 𝓑.p.IsHomLift (𝟙 S) (φ.map (pushforwardEndomorphism hA f r hr a)) :=
    isHomLift_basedFunctor_map φ (𝟙 S) _ (pushforwardEndomorphism_isHomLift hA f r hr a)
  have := hleft
  have := pushforwardEndomorphism_isHomLift (x' := fiberObj φ x') (x := fiberObj φ x) hB f
    (φ.map r) hrB ((mapFiberAut φ x') a)
  apply Aut.ext
  apply Iso.ext
  apply Functor.Fiber.hom_ext
  show φ.map (pushforwardEndomorphism hA f r hr a) =
    pushforwardEndomorphism (x' := fiberObj φ x') (x := fiberObj φ x) hB f (φ.map r) hrB
      ((mapFiberAut φ x') a)
  refine Functor.IsStronglyCocartesian.ext 𝓑.p f (φ.map r) (𝟙 S) ?_
  rw [← hom_comp_eq_comp_pushforwardEndomorphism (x' := fiberObj φ x') (x := fiberObj φ x)
    hB f (φ.map r) hrB ((mapFiberAut φ x') a)]
  rw [mapFiberAut_hom_val φ x' a, ← φ.toFunctor.map_comp, ← φ.toFunctor.map_comp,
    hom_comp_eq_comp_pushforwardEndomorphism hA f r hr a]

/-- The homomorphism of relative infinitesimal automorphism groups induced by a morphism over
the base: apply the morphism to an automorphism of the source of the lifting arrow. -/
public noncomputable def mapRelativeInfinitesimalAutomorphisms (φ : BasedFunctor 𝓐 𝓑)
    (hA : IsCofiberedInGroupoids 𝓐.p) (hB : IsCofiberedInGroupoids 𝓑.p)
    {R S : C} (f : R ⟶ S) {x' : 𝓐.p.Fiber R} {x : 𝓐.p.Fiber S}
    (r : x'.1 ⟶ x.1) (hr : 𝓐.p.IsHomLift f r) :
    relativeInfinitesimalAutomorphisms hA f r hr →
      relativeInfinitesimalAutomorphisms (x' := fiberObj φ x') (x := fiberObj φ x) hB f
        (φ.map r) (isHomLift_basedFunctor_map φ f r hr) :=
  fun a => ⟨(mapFiberAut φ x') a.1,
    (mem_relativeInfinitesimalAutomorphisms_iff (x' := fiberObj φ x') (x := fiberObj φ x) hB f
        (φ.map r) (isHomLift_basedFunctor_map φ f r hr) ((mapFiberAut φ x') a.1)).mpr
      (by
        change φ.map a.1.asIso.hom.val ≫ φ.map r = φ.map r
        rw [← φ.toFunctor.map_comp,
          (mem_relativeInfinitesimalAutomorphisms_iff hA f r hr a.1).mp a.2])⟩

/-- The automorphism underlying the image of a relative infinitesimal automorphism is the
image of the underlying automorphism. -/
public theorem mapRelativeInfinitesimalAutomorphisms_coe (φ : BasedFunctor 𝓐 𝓑)
    (hA : IsCofiberedInGroupoids 𝓐.p) (hB : IsCofiberedInGroupoids 𝓑.p)
    {R S : C} (f : R ⟶ S) {x' : 𝓐.p.Fiber R} {x : 𝓐.p.Fiber S}
    (r : x'.1 ⟶ x.1) (hr : 𝓐.p.IsHomLift f r)
    (a : relativeInfinitesimalAutomorphisms hA f r hr) :
    (mapRelativeInfinitesimalAutomorphisms φ hA hB f r hr a).1 = (mapFiberAut φ x') a.1 := rfl

/-- The image of a relative infinitesimal automorphism has as underlying arrow the image of
the underlying arrow. -/
public theorem mapRelativeInfinitesimalAutomorphisms_hom (φ : BasedFunctor 𝓐 𝓑)
    (hA : IsCofiberedInGroupoids 𝓐.p) (hB : IsCofiberedInGroupoids 𝓑.p)
    {R S : C} (f : R ⟶ S) {x' : 𝓐.p.Fiber R} {x : 𝓐.p.Fiber S}
    (r : x'.1 ⟶ x.1) (hr : 𝓐.p.IsHomLift f r)
    (a : relativeInfinitesimalAutomorphisms hA f r hr) :
    (mapRelativeInfinitesimalAutomorphisms φ hA hB f r hr a).1.asIso.hom.val =
      φ.map a.1.asIso.hom.val := rfl

/-- **Over a thin fibre the relative statement is a statement about automorphism groups.** If
a morphism over the base is surjective on the automorphisms of the source of a lifting arrow
whose target lies in a thin fibre, then it is surjective on relative infinitesimal
automorphisms along that arrow. -/
public theorem surjective_mapRelativeInfinitesimalAutomorphisms_of_surjective_mapFiberAut
    (φ : BasedFunctor 𝓐 𝓑) (hA : IsCofiberedInGroupoids 𝓐.p) (hB : IsCofiberedInGroupoids 𝓑.p)
    {R S : C} (f : R ⟶ S) {x' : 𝓐.p.Fiber R} {x : 𝓐.p.Fiber S}
    (r : x'.1 ⟶ x.1) (hr : 𝓐.p.IsHomLift f r) (hthin : Quiver.IsThin (𝓐.p.Fiber S))
    (h : Function.Surjective (mapFiberAut φ x')) :
    Function.Surjective (mapRelativeInfinitesimalAutomorphisms φ hA hB f r hr) := by
  intro b
  obtain ⟨a, ha⟩ := h b.1
  exact ⟨⟨a, mem_relativeInfinitesimalAutomorphisms_of_isThin hA f r hr hthin a⟩,
    Subtype.ext ha⟩

/-- **The converse over a thin fibre.** If a morphism over the base is surjective on relative
infinitesimal automorphisms along a lifting arrow whose target lies in a thin fibre of the
target category, then it is surjective on the automorphisms of the source. -/
public theorem surjective_mapFiberAut_of_surjective_mapRelativeInfinitesimalAutomorphisms
    (φ : BasedFunctor 𝓐 𝓑) (hA : IsCofiberedInGroupoids 𝓐.p) (hB : IsCofiberedInGroupoids 𝓑.p)
    {R S : C} (f : R ⟶ S) {x' : 𝓐.p.Fiber R} {x : 𝓐.p.Fiber S}
    (r : x'.1 ⟶ x.1) (hr : 𝓐.p.IsHomLift f r) (hthin : Quiver.IsThin (𝓑.p.Fiber S))
    (h : Function.Surjective (mapRelativeInfinitesimalAutomorphisms φ hA hB f r hr)) :
    Function.Surjective (mapFiberAut φ x') := by
  intro b
  obtain ⟨a, ha⟩ := h ⟨b, mem_relativeInfinitesimalAutomorphisms_of_isThin
    (x' := fiberObj φ x') (x := fiberObj φ x) hB f (φ.map r) (isHomLift_basedFunctor_map φ f r hr)
    hthin b⟩
  exact ⟨a.1, congrArg Subtype.val ha⟩

/-- **Surjectivity on automorphisms is invariant under isomorphism.** An isomorphism `u`
lying over an isomorphism of base objects carries the surjectivity of a morphism over the base
on automorphism groups from the source of `u` to its target. -/
public theorem surjective_mapFiberAut_of_isoOver (φ : BasedFunctor 𝓐 𝓑)
    (hA : IsCofiberedInGroupoids 𝓐.p) (hB : IsCofiberedInGroupoids 𝓑.p)
    {R R' : C} {y : 𝓐.p.Fiber R} {y' : 𝓐.p.Fiber R'} {e : R ≅ R'} (u : y.1 ≅ y'.1)
    (hu : 𝓐.p.IsHomLift e.hom u.hom) (hui : 𝓐.p.IsHomLift e.inv u.inv)
    (h : Function.Surjective (mapFiberAut φ y)) :
    Function.Surjective (mapFiberAut φ y') := by
  have huB : 𝓑.p.IsHomLift e.hom (φ.map u.hom) := isHomLift_basedFunctor_map φ e.hom u.hom hu
  have huiB : 𝓑.p.IsHomLift e.inv (φ.map u.inv) := isHomLift_basedFunctor_map φ e.inv u.inv hui
  let uB : (fiberObj φ y).1 ≅ (fiberObj φ y').1 := φ.toFunctor.mapIso u
  intro b
  obtain ⟨a, ha⟩ := h (pushforwardAutomorphism (x' := fiberObj φ y') (x := fiberObj φ y) hB
    e.inv uB.inv huiB b)
  refine ⟨pushforwardAutomorphism hA e.hom u.hom hu a, ?_⟩
  rw [mapFiberAut_pushforwardAutomorphism φ hA hB e.hom u.hom hu a, ha]
  exact pushforwardAutomorphism_pushforwardAutomorphism_inv hB uB huB huiB b

/-- **Pushforwards of one object along isomorphic arrows.** If `i : w ⟶ y` lies over
`s : p(w) ⟶ R` and `i' : w ⟶ y'` lies over `s ≫ e.hom` for an isomorphism `e : R ≅ R'` of
base objects, then surjectivity of a morphism over the base on the automorphisms of `y` gives
surjectivity on the automorphisms of `y'`. -/
public theorem surjective_mapFiberAut_of_pushforward (φ : BasedFunctor 𝓐 𝓑)
    (hA : IsCofiberedInGroupoids 𝓐.p) (hB : IsCofiberedInGroupoids 𝓑.p)
    {R R' : C} {w : 𝓐.obj} {y : 𝓐.p.Fiber R} {y' : 𝓐.p.Fiber R'}
    (s : 𝓐.p.obj w ⟶ R) (e : R ≅ R') (i : w ⟶ y.1) (hi : 𝓐.p.IsHomLift s i)
    (i' : w ⟶ y'.1) (hi' : 𝓐.p.IsHomLift (s ≫ e.hom) i')
    (h : Function.Surjective (mapFiberAut φ y)) :
    Function.Surjective (mapFiberAut φ y') := by
  have := hi
  have := hi'
  have := isStronglyCocartesian_of_isCofiberedInGroupoids hA s i hi
  let u : y.1 ⟶ y'.1 := Functor.IsStronglyCocartesian.map 𝓐.p s i
    (show s ≫ e.hom = s ≫ e.hom from rfl) i'
  have hu : 𝓐.p.IsHomLift e.hom u := inferInstance
  have hfac : 𝓐.p.map u = eqToHom y.2 ≫ e.hom ≫ eqToHom y'.2.symm :=
    IsHomLift.fac' 𝓐.p e.hom u
  have : IsIso (𝓐.p.map u) := by rw [hfac]; infer_instance
  have : IsIso u := isIso_of_isIso_map hA u
  have hui : 𝓐.p.IsHomLift e.inv (inv u) := by simpa using IsHomLift.inv 𝓐.p e.hom u
  exact surjective_mapFiberAut_of_isoOver φ hA hB (asIso u) hu hui h

end Map

/-! ### Naturality across a fibre square -/

section FibreSquare

variable {C : Type uC} [Category.{vC} C] {𝓐 : BasedCategory.{vA, uA} C}
  {𝓑 : BasedCategory.{vB, uB} C}
  {D A₁ A₂ A : C} {π₁ : D ⟶ A₁} {π₂ : D ⟶ A₂} {g₁ : A₁ ⟶ A} {g₂ : A₂ ⟶ A}
  {z : 𝓐.p.Fiber D} {x₁ : 𝓐.p.Fiber A₁} {x₂ : 𝓐.p.Fiber A₂} {x : 𝓐.p.Fiber A}
  {c₁ : z.1 ⟶ x₁.1} {c₂ : z.1 ⟶ x₂.1} {f₁ : x₁.1 ⟶ x.1} {f₂ : x₂.1 ⟶ x.1}

/-- **The naturality of the Tag 06JI identification across a fibre square.** Pushforward
along the second projection of a fibre square identifies the automorphisms of the square
trivial on the first projection with the infinitesimal automorphisms of the second factor
over the common target, and a morphism over the base commutes with that identification. -/
public theorem mapRelativeInfinitesimalAutomorphisms_fibreSquareHom (φ : BasedFunctor 𝓐 𝓑)
    (hA : IsCofiberedInGroupoids 𝓐.p) (hB : IsCofiberedInGroupoids 𝓑.p)
    (hc₁ : 𝓐.p.IsHomLift π₁ c₁) (hc₂ : 𝓐.p.IsHomLift π₂ c₂) (hf₂ : 𝓐.p.IsHomLift g₂ f₂)
    (hsq : IsPullback c₁ c₂ f₁ f₂)
    (hsqB : IsPullback (φ.map c₁) (φ.map c₂) (φ.map f₁) (φ.map f₂))
    (a : relativeInfinitesimalAutomorphisms hA π₁ c₁ hc₁) :
    mapRelativeInfinitesimalAutomorphisms φ hA hB g₂ f₂ hf₂
        (relativeInfinitesimalAutomorphismsFibreSquareHom hA hc₁ hc₂ hf₂ hsq a) =
      relativeInfinitesimalAutomorphismsFibreSquareHom (z := fiberObj φ z)
        (x₁ := fiberObj φ x₁) (x₂ := fiberObj φ x₂) (x := fiberObj φ x) hB
        (isHomLift_basedFunctor_map φ π₁ c₁ hc₁) (isHomLift_basedFunctor_map φ π₂ c₂ hc₂)
        (isHomLift_basedFunctor_map φ g₂ f₂ hf₂) hsqB
        (mapRelativeInfinitesimalAutomorphisms φ hA hB π₁ c₁ hc₁ a) :=
  Subtype.ext (mapFiberAut_pushforwardAutomorphism φ hA hB π₂ c₂ hc₂ a.1)

/-- **The two surjectivity statements of a fibre square agree.** For a fibre square lying over
a fibre square of the base whose image is again a fibre square, a morphism over the base is
surjective on the automorphisms of the square trivial on the first projection exactly when it
is surjective on the infinitesimal automorphisms of the second factor over the common
target. -/
public theorem surjective_mapRelativeInfinitesimalAutomorphisms_fibreSquare_iff
    (φ : BasedFunctor 𝓐 𝓑)
    (hA : IsCofiberedInGroupoids 𝓐.p) (hB : IsCofiberedInGroupoids 𝓑.p)
    (hc₁ : 𝓐.p.IsHomLift π₁ c₁) (hc₂ : 𝓐.p.IsHomLift π₂ c₂) (hf₂ : 𝓐.p.IsHomLift g₂ f₂)
    (hsq : IsPullback c₁ c₂ f₁ f₂)
    (hsqB : IsPullback (φ.map c₁) (φ.map c₂) (φ.map f₁) (φ.map f₂))
    (hbase : IsPullback π₁ π₂ g₁ g₂) :
    Function.Surjective (mapRelativeInfinitesimalAutomorphisms φ hA hB π₁ c₁ hc₁) ↔
      Function.Surjective (mapRelativeInfinitesimalAutomorphisms φ hA hB g₂ f₂ hf₂) := by
  have hnat := mapRelativeInfinitesimalAutomorphisms_fibreSquareHom φ hA hB hc₁ hc₂ hf₂
    hsq hsqB
  have hsurjB := relativeInfinitesimalAutomorphismsFibreSquareHom_surjective
    (z := fiberObj φ z) (x₁ := fiberObj φ x₁) (x₂ := fiberObj φ x₂) (x := fiberObj φ x) hB
    (isHomLift_basedFunctor_map φ π₁ c₁ hc₁) (isHomLift_basedFunctor_map φ π₂ c₂ hc₂)
    (isHomLift_basedFunctor_map φ g₂ f₂ hf₂) hsqB hbase
  have hinjB := relativeInfinitesimalAutomorphismsFibreSquareHom_injective
    (z := fiberObj φ z) (x₁ := fiberObj φ x₁) (x₂ := fiberObj φ x₂) (x := fiberObj φ x) hB
    (isHomLift_basedFunctor_map φ π₁ c₁ hc₁) (isHomLift_basedFunctor_map φ π₂ c₂ hc₂)
    (isHomLift_basedFunctor_map φ g₂ f₂ hf₂) hsqB
  have hsurjA := relativeInfinitesimalAutomorphismsFibreSquareHom_surjective hA hc₁ hc₂ hf₂
    hsq hbase
  constructor
  · intro h b
    obtain ⟨b', rfl⟩ := hsurjB b
    obtain ⟨a', ha'⟩ := h b'
    exact ⟨relativeInfinitesimalAutomorphismsFibreSquareHom hA hc₁ hc₂ hf₂ hsq a',
      (hnat a').trans (congrArg _ ha')⟩
  · intro h b'
    obtain ⟨a, ha⟩ := h (relativeInfinitesimalAutomorphismsFibreSquareHom
      (z := fiberObj φ z) (x₁ := fiberObj φ x₁) (x₂ := fiberObj φ x₂) (x := fiberObj φ x) hB
      (isHomLift_basedFunctor_map φ π₁ c₁ hc₁) (isHomLift_basedFunctor_map φ π₂ c₂ hc₂)
      (isHomLift_basedFunctor_map φ g₂ f₂ hf₂) hsqB b')
    obtain ⟨a', rfl⟩ := hsurjA a
    exact ⟨a', hinjB ((hnat a').symm.trans ha)⟩

/-- Let `z = x₁ ×_x x₂` be a fibre square lying over a fibre square of the base whose image
under a morphism `φ` over the base is again a fibre square, and let the common target lie in a
thin fibre. If `φ` is surjective on the automorphisms of `x₁` and of `x₂`, then it is surjective
on the automorphisms of `z`. -/
public theorem surjective_mapFiberAut_of_fibreSquare (φ : BasedFunctor 𝓐 𝓑)
    (hA : IsCofiberedInGroupoids 𝓐.p) (hB : IsCofiberedInGroupoids 𝓑.p)
    (hc₁ : 𝓐.p.IsHomLift π₁ c₁) (hc₂ : 𝓐.p.IsHomLift π₂ c₂)
    (hf₁ : 𝓐.p.IsHomLift g₁ f₁) (hf₂ : 𝓐.p.IsHomLift g₂ f₂)
    (hsq : IsPullback c₁ c₂ f₁ f₂)
    (hsqB : IsPullback (φ.map c₁) (φ.map c₂) (φ.map f₁) (φ.map f₂))
    (hbase : IsPullback π₁ π₂ g₁ g₂)
    (hthinA : Quiver.IsThin (𝓐.p.Fiber A))
    (h₁ : Function.Surjective (mapFiberAut φ x₁))
    (h₂ : Function.Surjective (mapFiberAut φ x₂)) :
    Function.Surjective (mapFiberAut φ z) := by
  have hc₁B := isHomLift_basedFunctor_map φ π₁ c₁ hc₁
  have hfirst : Function.Surjective
      (mapRelativeInfinitesimalAutomorphisms φ hA hB π₁ c₁ hc₁) :=
    (surjective_mapRelativeInfinitesimalAutomorphisms_fibreSquare_iff φ hA hB hc₁ hc₂ hf₂
      hsq hsqB hbase).2
      (surjective_mapRelativeInfinitesimalAutomorphisms_of_surjective_mapFiberAut φ hA hB
        g₂ f₂ hf₂ hthinA h₂)
  have hlift : ∀ α₁ : Aut x₁, ∃ a : Aut z, pushforwardAutomorphism hA π₁ c₁ hc₁ a = α₁ := by
    intro α₁
    obtain ⟨a, ha⟩ := relativeInfinitesimalAutomorphismsFibreSquareHom_surjective hA hc₂ hc₁
      hf₁ hsq.flip hbase.flip
      ⟨α₁, mem_relativeInfinitesimalAutomorphisms_of_isThin hA g₁ f₁ hf₁ hthinA α₁⟩
    exact ⟨a.1, congrArg Subtype.val ha⟩
  intro γ
  obtain ⟨α₁, hα₁⟩ := h₁ (pushforwardAutomorphism (x' := fiberObj φ z) (x := fiberObj φ x₁)
    hB π₁ (φ.map c₁) hc₁B γ)
  obtain ⟨a, ha⟩ := hlift α₁
  have hmapa : pushforwardAutomorphismHom (x' := fiberObj φ z) (x := fiberObj φ x₁) hB π₁
        (φ.map c₁) hc₁B ((mapFiberAut φ z) a) =
      pushforwardAutomorphismHom (x' := fiberObj φ z) (x := fiberObj φ x₁) hB π₁
        (φ.map c₁) hc₁B γ := by
    show pushforwardAutomorphism (x' := fiberObj φ z) (x := fiberObj φ x₁) hB π₁
      (φ.map c₁) hc₁B ((mapFiberAut φ z) a) = _
    rw [← mapFiberAut_pushforwardAutomorphism φ hA hB π₁ c₁ hc₁ a, ha]
    exact hα₁
  have hδmem : γ * ((mapFiberAut φ z) a)⁻¹ ∈
      relativeInfinitesimalAutomorphisms (x' := fiberObj φ z) (x := fiberObj φ x₁) hB π₁
        (φ.map c₁) hc₁B := by
    refine MonoidHom.mem_ker.2 ?_
    rw [map_mul, map_inv, hmapa, mul_inv_cancel]
  obtain ⟨b, hb⟩ := hfirst ⟨γ * ((mapFiberAut φ z) a)⁻¹, hδmem⟩
  have hbval : (mapFiberAut φ z) b.1 = γ * ((mapFiberAut φ z) a)⁻¹ :=
    congrArg Subtype.val hb
  exact ⟨b.1 * a, by rw [map_mul, hbval, inv_mul_cancel_right]⟩

end FibreSquare

end Deformation

end
