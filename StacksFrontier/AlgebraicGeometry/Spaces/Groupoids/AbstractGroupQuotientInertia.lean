module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Sigma.Basic
public import StacksCore.CategoryTheory.Inertia
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.AbstractGroupQuotientStack

/-!
# The inertia of a quotient by a commutative group (Stacks 0374)

Let `S` be a scheme, let `G` be a *commutative* group, let `Y → S` be a scheme over `S` and
let `a : G →* Aut Y` be an action of `G` on `Y` over `S`. For `g ∈ G` the source defines the
fixed-point scheme `Y^g = {y ∈ Y | g(y) = y}` as the fibre product
`Y^g = Y ×_{(1, 1), Y ×_S Y, (g, 1)} Y`, and asserts that the inertia stack of `[Y/G]` is
`∐_{g ∈ G} [Y^g/G]`.

This file constructs the fixed-point scheme `Y^g`, the action of `G` on it that exists
because `G` is commutative, and the canonical morphism of categories over
`(Sch/S)_fppf` from the disjoint union `∐_{g ∈ G} [Y^g/G]` to the inertia of `[Y/G]`, where
`[·/G]` is the quotient by an abstract group of Stacks 0371
(`AlgebraicGeometry.AbstractGroupQuotientStack`) and the inertia is Stacks 034I
(`CategoryTheory.AbsoluteInertia`). On `T`-points this morphism is the source's own recipe,
read in the direction that requires no local choice: a `G`-torsor `P → T` with a
`G`-equivariant `ψ : P → Y^g` is sent to the triple `(P, ι ∘ ψ, α)` with `ι : Y^g → Y` the
inclusion and `α` multiplication by `g` on `P`. That `α` is an automorphism of `(P, ι ∘ ψ)`
in `[Y/G]` is exactly the two facts the source uses: `G` commutative makes multiplication by
`g` equivariant, and `ι ∘ g = ι` makes it compatible with the equivariant map.

## Main definitions

* `AlgebraicGeometry.fixedScheme`: **Stacks 0374**, the scheme `Y^g`, as the displayed fibre
  product `Y ×_{(1, 1), Y ×_S Y, (g, 1)} Y`, with its inclusion
  `AlgebraicGeometry.fixedSchemeIncl` into `Y`.
* `AlgebraicGeometry.fixedSchemeAut`: **Stacks 0374**, the action of `G` on `Y^g` induced by
  the action on `Y`; this is where commutativity of `G` is used.
* `AlgebraicGeometry.schemePointsFunctor`: the functor of points of a scheme over `S` on the
  big fppf site, used to feed `Y` and `Y^g` to the quotient construction of Stacks 0371.
* `AlgebraicGeometry.fixedSchemeQuotient`: the quotient `[Y^g/G]`, the `g`-summand of the
  disjoint union, as `AlgebraicGeometry.AbstractGroupQuotientStack` applied to the functor of
  points of `Y^g`.
* `AlgebraicGeometry.AbstractGroupQuotientStack.mapTarget`: the functor
  `[[X/G]] ⥤ [[X'/G]]` attached to a `G`-equivariant map of sheaves `X → X'`.
* `AlgebraicGeometry.AbstractGroupQuotientStack.translation`: multiplication by `g` on the
  torsor of an object of `[[X/G]]`, as an automorphism of that object, available precisely
  when the equivariant map of the object is fixed by `g`.
* `AlgebraicGeometry.fixedQuotientToInertia` and
  `AlgebraicGeometry.AbstractGroupQuotientStack.inertiaComparison`: **Stacks 0374**, the
  morphism `∐_{g ∈ G} [Y^g/G] → I_{[Y/G]}`.

## Main results

* `AlgebraicGeometry.fixedSchemeHomEquiv`: **Stacks 0374**, the fibre product above is the
  locus `{y ∈ Y | g(y) = y}`: its `T`-points are the `T`-points `x` of `Y` with
  `x ≫ g = x`.
* `AlgebraicGeometry.fixedSchemeIncl_comp_aut`: `ι ≫ g = ι`, the defining identity of the
  fixed-point scheme.
* `AlgebraicGeometry.totalToTarget_factorsThroughFixedScheme`: the source's sentence
  "`φ ∘ α = φ` means that `φ` factors through the inclusion of `Y^g` in `Y`", for an object
  of `[[Y/G]]` whose equivariant map is fixed by `g`.
* `AlgebraicGeometry.AbstractGroupQuotientStack.inertiaComparison_comp_struct`: the
  comparison morphism is a morphism *over* `(Sch/S)_fppf`.

## Implementation notes

The source's displayed fibre product is taken literally: `Y ×_S Y` is the binary product
`Y ⨯ Y` of `Y` with itself in `Over S`, `(1, 1)` is `prod.lift (𝟙 Y) (𝟙 Y)` and `(g, 1)` is
`prod.lift (a g).hom (𝟙 Y)`. The second components of the two legs are the identity of `Y`,
so the two projections of the fibre product agree and two morphisms into `Y^g` that agree
after the inclusion are equal; the induced action is therefore built from `pullback.lift`,
with uniqueness a consequence, rather than chosen from an existence statement.

The quotient `[Y^g/G]` is `AlgebraicGeometry.AbstractGroupQuotientStack` applied to the
functor of points of `Y^g` restricted to the big fppf site of `S`. No containment assumption
on `Y^g` is needed for this: the functor of points is the presheaf `V ↦ (V ⟶ Y^g)` on the
site, formed in `Over S`, and `Y^g` itself never has to be an object of the site.

The automorphism `α` of the source is multiplication by `g` on the torsor. For this to be
equivariant for the whole constant sheaf of groups one needs the section attached to `g` to
be central, which is `CategoryTheory.constantSheafOfGroupsUnit_central`: conjugation by that
section is an endomorphism of the sheafification of the constant presheaf which is the
identity on the constant presheaf, hence the identity.

The equivalence itself is
`AlgebraicGeometry.inertia_equivalence_stackCoproduct` in
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.AbstractGroupQuotientInertiaEquivalence`. There the
disjoint union of the formula is the coproduct of *stacks*, the stackification of the disjoint
union of categories `Σ g, [Y^g/G]` used here: the source only produces the element `g` with `α`
equal to multiplication by `g` locally in the fppf topology over `T`, and the plain disjoint union
is not equivalent to the inertia stack.

## References

* [Stacks Project, Tag 0374](https://stacks.math.columbia.edu/tag/0374)
* [Stacks Project, Tag 0371](https://stacks.math.columbia.edu/tag/0371)
* [Stacks Project, Tag 034I](https://stacks.math.columbia.edu/tag/034I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

universe w v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (G : Type w)

/-- The sections of the constant sheaf of groups attached to a group element are compatible
with restriction: they are the images of the unit of sheafification, which is natural. -/
lemma constantSheafOfGroupsUnit_naturality [Group G] [HasWeakSheafify J GrpCat.{w}]
    {V W : Cᵒᵖ} (h : V ⟶ W) (g : G) :
    (constantSheafOfGroups J G).presheaf.map h (constantSheafOfGroupsUnit J G V g) =
      constantSheafOfGroupsUnit J G W g :=
  ((toSheafify J ((Functor.const Cᵒᵖ).obj (GrpCat.of G))).naturality_apply h g).symm

/-- For a commutative group `G` the sections of the constant sheaf of groups coming from
elements of `G` are central. Conjugation by such a section is an endomorphism of the
sheafification of the constant presheaf which restricts to the identity on the constant
presheaf, hence is the identity. -/
lemma constantSheafOfGroupsUnit_central [CommGroup G] [HasWeakSheafify J GrpCat.{w}]
    (V : Cᵒᵖ) (g : G) (γ : (constantSheafOfGroups J G).presheaf.obj V) :
    constantSheafOfGroupsUnit J G V g * γ = γ * constantSheafOfGroupsUnit J G V g := by
  set P := (Functor.const Cᵒᵖ).obj (GrpCat.of G) with hP
  set H := sheafify J P with hH
  set η := toSheafify J P with hη
  have hn {V W : Cᵒᵖ} (f : V ⟶ W) (x : G) :
      (H.map f).hom ((η.app V).hom x) = (η.app W).hom x :=
    (η.naturality_apply f x).symm
  let c : H ⟶ H :=
    { app := fun W => GrpCat.ofHom (MulAut.conj ((η.app W).hom g)).toMonoidHom
      naturality := by
        intro W W' f
        ext δ
        change (η.app W').hom g * (H.map f).hom δ * ((η.app W').hom g)⁻¹ =
          (H.map f).hom ((η.app W).hom g * δ * ((η.app W).hom g)⁻¹)
        simp only [map_mul, map_inv, hn] }
  have hc : c = 𝟙 H := by
    apply sheafify_hom_ext J c (𝟙 H) ((presheafToSheaf J GrpCat).obj P).property
    ext W x
    change (η.app W).hom g * (η.app W).hom x * ((η.app W).hom g)⁻¹ = (η.app W).hom x
    rw [← map_mul, mul_comm g x, map_mul]
    simp [mul_assoc]
  change H.obj V at γ
  change (η.app V).hom g * γ = γ * (η.app V).hom g
  have he := congrArg (fun k : H ⟶ H => (k.app V).hom γ) hc
  change (η.app V).hom g * γ * ((η.app V).hom g)⁻¹ = γ at he
  have he' := congrArg (fun x => x * (η.app V).hom g) he
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using he'

end CategoryTheory

namespace AlgebraicGeometry

universe t z w u

section FixedScheme

variable (S : Scheme.{u}) (G : Type w) [CommGroup G]

/-- **Stacks 0374.** The fixed-point scheme `Y^g = {y ∈ Y | g(y) = y}` of the automorphism
of `Y` attached to a group element `g`, as the fibre product
`Y^g = Y ×_{(1, 1), Y ×_S Y, (g, 1)} Y` displayed in the source. -/
@[stacks 0374 "the fixed-point scheme X^g as the displayed fibre product"]
def fixedScheme (Y : Over S) (a : G →* Aut Y) (g : G) : Over S :=
  pullback (prod.lift (𝟙 Y) (𝟙 Y)) (prod.lift (a g).hom (𝟙 Y))

/-- The inclusion `Y^g → Y` of the fixed-point scheme, the first projection of the fibre
product defining it. -/
def fixedSchemeIncl (Y : Over S) (a : G →* Aut Y) (g : G) : fixedScheme S G Y a g ⟶ Y :=
  pullback.fst _ _

variable {S G}

/-- Both projections of the fibre product defining `Y^g` agree, because the second
components of the two legs are the identity of `Y`. -/
lemma fixedSchemeIncl_eq_snd (Y : Over S) (a : G →* Aut Y) (g : G) :
    fixedSchemeIncl S G Y a g = pullback.snd _ _ := by
  have h := pullback.condition (f := prod.lift (𝟙 Y) (𝟙 Y)) (g := prod.lift (a g).hom (𝟙 Y))
  have h2 := congrArg (· ≫ (prod.snd : Y ⨯ Y ⟶ Y)) h
  simp only [Category.assoc, prod.lift_snd, Category.comp_id] at h2
  exact h2

/-- The defining identity of the fixed-point scheme: the automorphism attached to `g` acts
as the identity on `Y^g`. -/
lemma fixedSchemeIncl_comp_aut (Y : Over S) (a : G →* Aut Y) (g : G) :
    fixedSchemeIncl S G Y a g ≫ (a g).hom = fixedSchemeIncl S G Y a g := by
  have h := pullback.condition (f := prod.lift (𝟙 Y) (𝟙 Y)) (g := prod.lift (a g).hom (𝟙 Y))
  have h1 := congrArg (· ≫ (prod.fst : Y ⨯ Y ⟶ Y)) h
  simp only [Category.assoc, prod.lift_fst, Category.comp_id] at h1
  conv_lhs => rw [fixedSchemeIncl_eq_snd]
  exact h1.symm

/-- Two morphisms into `Y^g` that agree after composing with the inclusion into `Y` are
equal: the inclusion is a monomorphism, both legs of the defining fibre product being split
monomorphisms. -/
lemma fixedScheme_hom_ext {Y : Over S} {a : G →* Aut Y} {g : G} {T : Over S}
    {φ ψ : T ⟶ fixedScheme S G Y a g}
    (h : φ ≫ fixedSchemeIncl S G Y a g = ψ ≫ fixedSchemeIncl S G Y a g) : φ = ψ := by
  refine pullback.hom_ext h ?_
  rw [← fixedSchemeIncl_eq_snd]
  exact h

/-- A `T`-point of `Y` fixed by `g` lifts to a `T`-point of the fixed-point scheme. -/
def fixedSchemeLift {Y : Over S} {a : G →* Aut Y} {g : G} {T : Over S} (x : T ⟶ Y)
    (hx : x ≫ (a g).hom = x) : T ⟶ fixedScheme S G Y a g :=
  pullback.lift x x (by ext <;> simp [hx])

/-- The lift of a fixed `T`-point `x` of `Y` to `Y^g` composes with the inclusion to `x`. -/
@[simp]
lemma fixedSchemeLift_comp_incl {Y : Over S} {a : G →* Aut Y} {g : G} {T : Over S} (x : T ⟶ Y)
    (hx : x ≫ (a g).hom = x) :
    fixedSchemeLift (a := a) (g := g) x hx ≫ fixedSchemeIncl S G Y a g = x :=
  pullback.lift_fst _ _ _

/-- **Stacks 0374.** The fibre product `Y ×_{(1, 1), Y ×_S Y, (g, 1)} Y` is the locus
`Y^g = {y ∈ Y | g(y) = y}`: its `T`-points are exactly the `T`-points of `Y` fixed by the
automorphism attached to `g`. -/
@[stacks 0374 "X^g = {x ∈ X | g(x) = x} as a functor of points"]
def fixedSchemeHomEquiv (Y : Over S) (a : G →* Aut Y) (g : G) (T : Over S) :
    (T ⟶ fixedScheme S G Y a g) ≃ {x : T ⟶ Y // x ≫ (a g).hom = x} where
  toFun φ := ⟨φ ≫ fixedSchemeIncl S G Y a g, by
    rw [Category.assoc, fixedSchemeIncl_comp_aut]⟩
  invFun x := fixedSchemeLift x.1 x.2
  left_inv φ := fixedScheme_hom_ext (by simp)
  right_inv x := Subtype.ext (by simp)

/-- Two automorphisms of `Y` attached to group elements commute, because `G` does. -/
lemma aut_hom_comm_of_commGroup (Y : Over S) (a : G →* Aut Y) (g h : G) :
    (a h).hom ≫ (a g).hom = (a g).hom ≫ (a h).hom := by
  have hgh : a g * a h = a h * a g := by rw [← map_mul, ← map_mul, mul_comm]
  exact congrArg Iso.hom hgh

/-- The endomorphism of `Y^g` induced by the automorphism of `Y` attached to `h`. It exists
because `G` is commutative: `h` carries the locus fixed by `g` into itself. -/
def fixedSchemeMap (Y : Over S) (a : G →* Aut Y) (g h : G) :
    fixedScheme S G Y a g ⟶ fixedScheme S G Y a g :=
  fixedSchemeLift (fixedSchemeIncl S G Y a g ≫ (a h).hom) (by
    rw [Category.assoc, aut_hom_comm_of_commGroup, ← Category.assoc,
      fixedSchemeIncl_comp_aut])

/-- The endomorphism of `Y^g` induced by `h`, followed by the inclusion into `Y`, is the
inclusion followed by the automorphism of `Y` attached to `h`. -/
@[simp]
lemma fixedSchemeMap_comp_incl (Y : Over S) (a : G →* Aut Y) (g h : G) :
    fixedSchemeMap Y a g h ≫ fixedSchemeIncl S G Y a g =
      fixedSchemeIncl S G Y a g ≫ (a h).hom :=
  fixedSchemeLift_comp_incl _ _

/-- The endomorphism of `Y^g` induced by the identity of `G` is the identity. -/
lemma fixedSchemeMap_one (Y : Over S) (a : G →* Aut Y) (g : G) :
    fixedSchemeMap Y a g 1 = 𝟙 _ := by
  refine fixedScheme_hom_ext ?_
  rw [fixedSchemeMap_comp_incl, map_one, Category.id_comp]
  exact Category.comp_id _

/-- The endomorphism of `Y^g` induced by `h * k` is the composite of those induced by `k`
and by `h`. -/
lemma fixedSchemeMap_mul (Y : Over S) (a : G →* Aut Y) (g h k : G) :
    fixedSchemeMap Y a g (h * k) = fixedSchemeMap Y a g k ≫ fixedSchemeMap Y a g h := by
  refine fixedScheme_hom_ext ?_
  rw [Category.assoc, fixedSchemeMap_comp_incl, fixedSchemeMap_comp_incl, ← Category.assoc,
    fixedSchemeMap_comp_incl, map_mul, Category.assoc]
  rfl

/-- **Stacks 0374.** The action of `G` on the fixed-point scheme `Y^g` induced by the action
on `Y`. It is here that commutativity of `G` enters: for `h ∈ G` the automorphism of `Y`
attached to `h` commutes with the one attached to `g`, hence preserves `Y^g`. -/
@[stacks 0374 "the induced action of G on X^g"]
def fixedSchemeAut (Y : Over S) (a : G →* Aut Y) (g : G) :
    G →* Aut (fixedScheme S G Y a g) where
  toFun h :=
    { hom := fixedSchemeMap Y a g h
      inv := fixedSchemeMap Y a g h⁻¹
      hom_inv_id := by rw [← fixedSchemeMap_mul, inv_mul_cancel, fixedSchemeMap_one]
      inv_hom_id := by rw [← fixedSchemeMap_mul, mul_inv_cancel, fixedSchemeMap_one] }
  map_one' := Aut.ext (fixedSchemeMap_one Y a g)
  map_mul' h k := Aut.ext (fixedSchemeMap_mul Y a g h k)

/-- The automorphism of `Y^g` attached to `h` has underlying morphism `fixedSchemeMap Y a g h`. -/
@[simp]
lemma fixedSchemeAut_hom (Y : Over S) (a : G →* Aut Y) (g h : G) :
    (fixedSchemeAut Y a g h).hom = fixedSchemeMap Y a g h := rfl

end FixedScheme

section Points

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The functor of points of a scheme over `S`, restricted to the big fppf site
`(Sch/S)_fppf`: a scheme `Z` over `S` goes to the presheaf `V ↦ (V ⟶ Z)` of morphisms over
`S`. This is how a scheme over `S` which need not be an object of the site — such as the
fixed-point scheme `Y^g` — is fed to the quotient construction of Stacks 0371. -/
def schemePointsFunctor : Over S ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj (Over.post B.inclusion).op

variable (G : Type w) [CommGroup G]

/-- The action of `G` on the functor of points of a scheme over `S` induced by an action of
`G` on that scheme. -/
def schemePointsAut (Z : Over S) (b : G →* Aut Z) :
    G →* Aut ((schemePointsFunctor B S hS).obj Z) :=
  (Functor.mapAut Z (schemePointsFunctor B S hS)).comp b

/-- The automorphism of the functor of points attached to `g` is the image under
`schemePointsFunctor` of the automorphism of `Z` attached to `g`. -/
@[simp]
lemma schemePointsAut_hom (Z : Over S) (b : G →* Aut Z) (g : G) :
    (schemePointsAut B S hS G Z b g).hom = (schemePointsFunctor B S hS).map (b g).hom := rfl

end Points

namespace AbstractGroupQuotientStack

section MapTarget

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {G : Type w} [Group G]
  [HasWeakSheafify (BigFppfOver.topology B S hS) GrpCat.{w}]
  {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type z} {ρ : G →* Aut X} {ρ' : G →* Aut X'}

/-- The functor `[[X/G]] ⥤ [[X'/G]]` attached to a `G`-equivariant map of sheaves
`u : X → X'`: it keeps the object of the site and the torsor of a triple and composes its
equivariant map with `u`. -/
def mapTarget (u : X ⟶ X') (hu : ∀ g : G, (ρ g).hom ≫ u = u ≫ (ρ' g).hom) :
    AbstractGroupQuotientStack.{t} B S hS G X ρ ⥤
      AbstractGroupQuotientStack.{t} B S hS G X' ρ' where
  obj A :=
    { base := A.base
      torsor := A.torsor
      isTorsor := A.isTorsor
      toTarget := fun W s => u.app (op W.unop.left) (A.toTarget W s)
      toTarget_naturality := fun h s => by
        rw [A.toTarget_naturality h s]
        exact NatTrans.naturality_apply u _ _
      toTarget_equivariant := fun W g s => by
        rw [A.toTarget_equivariant W g s]
        have h2 := congrArg (fun n : X ⟶ X' => n.app (op W.unop.left) (A.toTarget W s)) (hu g)
        simpa only [NatTrans.comp_app_apply] using h2 }
  map {_ _} f :=
    { base := f.base
      map := f.map
      map_naturality := f.map_naturality
      map_equivariant := f.map_equivariant
      bijOn_map := f.bijOn_map
      totalToTarget_comp := fun V p => congrArg (u.app V) (f.totalToTarget_comp V p) }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The equivariant map on total spaces of the image of `A` under `mapTarget u hu` is that of
`A` followed by `u`. -/
@[simp]
lemma mapTarget_obj_totalToTarget (u : X ⟶ X')
    (hu : ∀ g : G, (ρ g).hom ≫ u = u ≫ (ρ' g).hom)
    (A : AbstractGroupQuotientStack.{t} B S hS G X ρ) (V : (BigFppfOver B S hS)ᵒᵖ)
    (p : A.Total V) :
    ((mapTarget u hu).obj A).totalToTarget V p = u.app V (A.totalToTarget V p) := rfl

/-- The functor attached to an equivariant map of sheaves is a functor over the big fppf
site: it does not change the object of the site under a triple. -/
lemma mapTarget_comp_projection (u : X ⟶ X')
    (hu : ∀ g : G, (ρ g).hom ≫ u = u ≫ (ρ' g).hom) :
    mapTarget.{t} u hu ⋙ projection (ρ := ρ') = projection (ρ := ρ) := rfl

end MapTarget

section Translation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {G : Type w} [CommGroup G]
  [HasWeakSheafify (BigFppfOver.topology B S hS) GrpCat.{w}]
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type z} {ρ : G →* Aut X}
  (A : AbstractGroupQuotientStack.{t} B S hS G X ρ)

/-- The action of a section `γ` on the total space of the torsor of `A` lies over the same
object of the site. -/
@[simp]
lemma totalSmul_fst {V : (BigFppfOver B S hS)ᵒᵖ}
    (γ : (constantSheafOfGroups (BigFppfOver.topology B S hS) G).presheaf.obj V)
    (p : A.Total V) : (A.totalSmul γ p).1 = p.1 := rfl

/-- The identity section acts trivially on the total space of the torsor of `A`. -/
lemma totalSmul_one {V : (BigFppfOver B S hS)ᵒᵖ} (p : A.Total V) : A.totalSmul 1 p = p :=
  congrArg (fun s => (⟨p.1, s⟩ : A.Total V)) (A.torsor.one_act _ p.2)

/-- The action on the total space of the torsor of `A` is compatible with multiplication of
sections: `(γ * δ) • p = γ • (δ • p)`. -/
lemma totalSmul_mul {V : (BigFppfOver B S hS)ᵒᵖ}
    (γ δ : (constantSheafOfGroups (BigFppfOver.topology B S hS) G).presheaf.obj V)
    (p : A.Total V) : A.totalSmul (γ * δ) p = A.totalSmul γ (A.totalSmul δ p) :=
  congrArg (fun s => (⟨p.1, s⟩ : A.Total V))
    (A.torsor.mul_act (op (Over.mk p.1)) γ δ p.2)

/-- The action on the total space of the torsor of `A` commutes with restriction along
`h : V ⟶ W`, the section `γ` being restricted along `h` as well. -/
lemma totalMap_totalSmul {V W : (BigFppfOver B S hS)ᵒᵖ} (h : V ⟶ W)
    (γ : (constantSheafOfGroups (BigFppfOver.topology B S hS) G).presheaf.obj V)
    (p : A.Total V) :
    A.totalMap h (A.totalSmul γ p) =
      A.totalSmul ((constantSheafOfGroups (BigFppfOver.topology B S hS) G).presheaf.map h γ)
        (A.totalMap h p) :=
  congrArg (fun s => (⟨h.unop ≫ p.1, s⟩ : A.Total W))
    (A.torsor.naturality (Over.homMk h.unop :
      Over.mk (h.unop ≫ p.1) ⟶ Over.mk p.1).op γ p.2)

/-- Multiplication by `g ∈ G` on the torsor of an object of `[[X/G]]`, read on total
spaces. -/
def translationMap (g : G) (V : (BigFppfOver B S hS)ᵒᵖ) (p : A.Total V) : A.Total V :=
  A.totalSmul (constantSheafOfGroupsUnit (BigFppfOver.topology B S hS) G V g) p

/-- Multiplication by `g` on the total space of the torsor of `A` lies over the same object
of the site. -/
@[simp]
lemma translationMap_fst (g : G) (V : (BigFppfOver B S hS)ᵒᵖ) (p : A.Total V) :
    (A.translationMap g V p).1 = p.1 := rfl

/-- Multiplication by the identity of `G` on the total space of the torsor of `A` is the
identity. -/
@[simp]
lemma translationMap_one (V : (BigFppfOver B S hS)ᵒᵖ) (p : A.Total V) :
    A.translationMap 1 V p = p := by
  rw [translationMap, map_one, totalSmul_one]

/-- Multiplication by `h` and then by `g` on the total space of the torsor of `A` is
multiplication by `g * h`. -/
lemma translationMap_mul (g h : G) (V : (BigFppfOver B S hS)ᵒᵖ) (p : A.Total V) :
    A.translationMap g V (A.translationMap h V p) = A.translationMap (g * h) V p := by
  rw [translationMap, translationMap, translationMap, map_mul, totalSmul_mul]

/-- Multiplication by `g` on the torsor of an object of `[[X/G]]` is a bijection of total
spaces, with inverse multiplication by `g⁻¹`. -/
lemma translationMap_translationMap_inv (g : G) (V : (BigFppfOver B S hS)ᵒᵖ)
    (p : A.Total V) : A.translationMap g⁻¹ V (A.translationMap g V p) = p := by
  rw [translationMap_mul, inv_mul_cancel, translationMap_one]

variable {A}

/-- **Multiplication by `g` as an endomorphism of an object of `[[X/G]]`.** For an object
`A = (U, P, φ)` of `[[X/G]]`, multiplication by `g` on `P` is a morphism `A ⟶ A` over the
identity of `U` exactly when `φ` is fixed by `g`. Equivariance for the whole constant sheaf
of groups holds because `G` is commutative. -/
def translationHom (g : G)
    (hA : ∀ (V : (BigFppfOver B S hS)ᵒᵖ) (p : A.Total V),
      (ρ g).hom.app V (A.totalToTarget V p) = A.totalToTarget V p) : A ⟶ A where
  base := 𝟙 A.base
  map := A.translationMap g
  map_naturality := fun {V W} h p => by
    rw [translationMap, translationMap, totalMap_totalSmul,
      constantSheafOfGroupsUnit_naturality]
  map_equivariant := fun V γ p => by
    rw [translationMap, translationMap, ← totalSmul_mul, ← totalSmul_mul,
      constantSheafOfGroupsUnit_central]
  bijOn_map := fun V c => by
    refine ⟨fun p hp => ?_, fun p _ q _ hpq => ?_, fun q hq => ?_⟩
    · change (A.translationMap g V p).1 = c ≫ 𝟙 A.base
      rw [translationMap_fst, Category.comp_id]
      exact hp
    · have h := congrArg (A.translationMap g⁻¹ V) hpq
      rwa [translationMap_translationMap_inv, translationMap_translationMap_inv] at h
    · refine ⟨A.translationMap g⁻¹ V q, ?_, ?_⟩
      · change (A.translationMap g⁻¹ V q).1 = c
        rw [translationMap_fst]
        simpa only [Set.mem_ofPred_eq, Category.comp_id] using hq
      · rw [translationMap_mul, mul_inv_cancel, translationMap_one]
  totalToTarget_comp := fun V p => by
    rw [translationMap, totalSmul]
    exact (A.toTarget_equivariant (op (Over.mk p.1)) g p.2).trans (hA V p)

/-- The endomorphism `translationHom g hA` lies over the identity of `A.base`. -/
@[simp]
lemma translationHom_base (g : G)
    (hA : ∀ (V : (BigFppfOver B S hS)ᵒᵖ) (p : A.Total V),
      (ρ g).hom.app V (A.totalToTarget V p) = A.totalToTarget V p) :
    (translationHom g hA).base = 𝟙 A.base := rfl

/-- The map on total spaces of `translationHom g hA` is multiplication by `g`. -/
@[simp]
lemma translationHom_map (g : G)
    (hA : ∀ (V : (BigFppfOver B S hS)ᵒᵖ) (p : A.Total V),
      (ρ g).hom.app V (A.totalToTarget V p) = A.totalToTarget V p) :
    (translationHom g hA).map = A.translationMap g := rfl

/-- If the equivariant map of an object of `[[X/G]]` is fixed by `g` then it is fixed by
`g⁻¹`. -/
lemma totalToTarget_fixed_inv {g : G}
    (hA : ∀ (V : (BigFppfOver B S hS)ᵒᵖ) (p : A.Total V),
      (ρ g).hom.app V (A.totalToTarget V p) = A.totalToTarget V p)
    (V : (BigFppfOver B S hS)ᵒᵖ) (p : A.Total V) :
    (ρ g⁻¹).hom.app V (A.totalToTarget V p) = A.totalToTarget V p := by
  have h0 : (ρ g).hom ≫ (ρ g⁻¹).hom = 𝟙 X :=
    congrArg Iso.hom (show ρ g⁻¹ * ρ g = 1 by rw [← map_mul, inv_mul_cancel, map_one])
  have h1 : (ρ g⁻¹).hom.app V ((ρ g).hom.app V (A.totalToTarget V p)) =
      A.totalToTarget V p := by
    simpa using types_congr_hom (NatTrans.congr_app h0 V) (A.totalToTarget V p)
  rwa [hA V p] at h1

/-- **Multiplication by `g` as an automorphism of an object of `[[X/G]]`**, the automorphism
`α` of the source: its inverse is multiplication by `g⁻¹`. -/
def translation (g : G)
    (hA : ∀ (V : (BigFppfOver B S hS)ᵒᵖ) (p : A.Total V),
      (ρ g).hom.app V (A.totalToTarget V p) = A.totalToTarget V p) : Aut A where
  hom := translationHom g hA
  inv := translationHom g⁻¹ (totalToTarget_fixed_inv hA)
  hom_inv_id := Hom.ext (Category.id_comp _) (by
    funext V p
    change A.translationMap g⁻¹ V (A.translationMap g V p) = p
    exact A.translationMap_translationMap_inv g V p)
  inv_hom_id := Hom.ext (Category.id_comp _) (by
    funext V p
    change A.translationMap g V (A.translationMap g⁻¹ V p) = p
    rw [translationMap_mul, mul_inv_cancel, translationMap_one])

/-- Multiplication by `g` lies over the identity of the object of the site, so it is an
automorphism in the sense of the inertia of Stacks 034I. -/
@[simp]
lemma projection_map_translation (g : G)
    (hA : ∀ (V : (BigFppfOver B S hS)ᵒᵖ) (p : A.Total V),
      (ρ g).hom.app V (A.totalToTarget V p) = A.totalToTarget V p) :
    (projection (ρ := ρ)).map (translation g hA).hom = 𝟙 A.base := rfl

end Translation

end AbstractGroupQuotientStack

section Inertia

open AbstractGroupQuotientStack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (G : Type w) [CommGroup G]
  [HasWeakSheafify (BigFppfOver.topology B S hS) GrpCat.{w}] (Y : Over S) (a : G →* Aut Y)

/-- The quotient `[Y/G]` of a scheme over `S` by an abstract group action, as the quotient of
Stacks 0371 of its functor of points. -/
abbrev schemeQuotient (Z : Over S) (b : G →* Aut Z) :=
  AbstractGroupQuotientStack.{t} B S hS G ((schemePointsFunctor B S hS).obj Z)
    (schemePointsAut B S hS G Z b)

/-- The projection of `[Z/G]` to the big fppf site, which is what makes it a category over
`(Sch/S)_fppf`. -/
abbrev schemeQuotientProjection (Z : Over S) (b : G →* Aut Z) :
    schemeQuotient.{t} B S hS G Z b ⥤ BigFppfOver B S hS :=
  AbstractGroupQuotientStack.projection (B := B) (S := S) (hS := hS) (G := G)
    (X := (schemePointsFunctor B S hS).obj Z) (ρ := schemePointsAut B S hS G Z b)

/-- The quotient `[Y^g/G]` of the fixed-point scheme of `g` by the induced action, the
`g`-summand of the disjoint union in the formula of Stacks 0374. -/
abbrev fixedSchemeQuotient (g : G) :=
  schemeQuotient.{t} B S hS G (fixedScheme S G Y a g) (fixedSchemeAut Y a g)

/-- The map `Y^g → Y` on functors of points, which is equivariant for the induced action on
`Y^g` and the given action on `Y`. -/
def fixedSchemePointsIncl (g : G) :
    (schemePointsFunctor B S hS).obj (fixedScheme S G Y a g) ⟶
      (schemePointsFunctor B S hS).obj Y :=
  (schemePointsFunctor B S hS).map (fixedSchemeIncl S G Y a g)

omit [HasWeakSheafify (BigFppfOver.topology B S hS) GrpCat.{w}] in
/-- The map `Y^g → Y` on functors of points is `G`-equivariant for the induced action on
`Y^g` and the given action on `Y`. -/
lemma fixedSchemePointsIncl_equivariant (g : G) (h : G) :
    (schemePointsAut B S hS G (fixedScheme S G Y a g) (fixedSchemeAut Y a g) h).hom ≫
        fixedSchemePointsIncl B S hS G Y a g =
      fixedSchemePointsIncl B S hS G Y a g ≫ (schemePointsAut B S hS G Y a h).hom := by
  rw [schemePointsAut_hom, schemePointsAut_hom, fixedSchemePointsIncl, fixedSchemeAut_hom,
    ← Functor.map_comp, ← Functor.map_comp, fixedSchemeMap_comp_incl]

omit [HasWeakSheafify (BigFppfOver.topology B S hS) GrpCat.{w}] in
/-- The map `Y^g → Y` on functors of points, followed by the automorphism attached to `g`, is
the map `Y^g → Y` itself. -/
lemma fixedSchemePointsIncl_comp_aut (g : G) :
    fixedSchemePointsIncl B S hS G Y a g ≫ (schemePointsAut B S hS G Y a g).hom =
      fixedSchemePointsIncl B S hS G Y a g := by
  rw [schemePointsAut_hom, fixedSchemePointsIncl, ← Functor.map_comp,
    fixedSchemeIncl_comp_aut]

/-- The functor `[Y^g/G] ⥤ [Y/G]` composing the equivariant map of a triple with the
inclusion `Y^g → Y`. -/
def fixedSchemeQuotientToQuotient (g : G) :
    fixedSchemeQuotient.{t} B S hS G Y a g ⥤ schemeQuotient.{t} B S hS G Y a :=
  mapTarget (fixedSchemePointsIncl B S hS G Y a g)
    (fixedSchemePointsIncl_equivariant B S hS G Y a g)

/-- The equivariant map of a triple of `[Y^g/G]`, pushed into `[Y/G]`, is fixed by `g`: this
is `ι ≫ g = ι` for the inclusion `ι : Y^g → Y`. -/
lemma totalToTarget_fixed (g : G) (A : fixedSchemeQuotient.{t} B S hS G Y a g)
    (V : (BigFppfOver B S hS)ᵒᵖ)
    (p : ((fixedSchemeQuotientToQuotient.{t} B S hS G Y a g).obj A).Total V) :
    (schemePointsAut B S hS G Y a g).hom.app V
        (((fixedSchemeQuotientToQuotient.{t} B S hS G Y a g).obj A).totalToTarget V p) =
      ((fixedSchemeQuotientToQuotient.{t} B S hS G Y a g).obj A).totalToTarget V p := by
  exact types_congr_hom (NatTrans.congr_app (fixedSchemePointsIncl_comp_aut B S hS G Y a g) V) _

/-- **Stacks 0374.** The source's sentence "the condition that `φ ∘ α = φ` means that `φ`
factors through the inclusion of `Y^g` in `Y`": for an object of `[Y/G]` whose equivariant
map is fixed by `g`, every value of that map factors uniquely through `Y^g`. -/
@[stacks 0374 "φ ∘ α = φ makes φ factor through the inclusion of X^g in X"]
theorem totalToTarget_factorsThroughFixedScheme (g : G)
    (A : schemeQuotient.{t} B S hS G Y a)
    (hA : ∀ (V : (BigFppfOver B S hS)ᵒᵖ) (p : A.Total V),
      (schemePointsAut B S hS G Y a g).hom.app V (A.totalToTarget V p) =
        A.totalToTarget V p)
    (V : (BigFppfOver B S hS)ᵒᵖ) (p : A.Total V) :
    ∃! y : (Over.post B.inclusion).obj V.unop ⟶ fixedScheme S G Y a g,
      y ≫ fixedSchemeIncl S G Y a g = A.totalToTarget V p := by
  refine ⟨fixedSchemeLift (A.totalToTarget V p) (hA V p),
    fixedSchemeLift_comp_incl _ _, fun y hy => ?_⟩
  exact fixedScheme_hom_ext (S := S) (G := G)
    (hy.trans (fixedSchemeLift_comp_incl _ _).symm)

/-- **Stacks 0374.** The morphism `[Y^g/G] → I_{[Y/G]}` of the source: a torsor `P` with a
`G`-equivariant map `ψ : P → Y^g` goes to the triple `(P, ι ∘ ψ)` together with the
automorphism given by multiplication by `g` on `P`. -/
@[stacks 0374 "the g-th summand of the morphism to the inertia stack"]
def fixedQuotientToInertia (g : G) :
    fixedSchemeQuotient.{t} B S hS G Y a g ⥤
      AbsoluteInertia (schemeQuotientProjection.{t} B S hS G Y a) where
  obj A :=
    { obj := (fixedSchemeQuotientToQuotient.{t} B S hS G Y a g).obj A
      auto := translation g (totalToTarget_fixed.{t} B S hS G Y a g A)
      cond := rfl }
  map {A A'} f :=
    { hom := (fixedSchemeQuotientToQuotient.{t} B S hS G Y a g).map f
      comm := Hom.ext (by
        change f.base ≫ 𝟙 A'.base = 𝟙 A.base ≫ f.base
        rw [Category.comp_id, Category.id_comp]) (by
        funext V p
        change A'.translationMap g V (f.map V p) = f.map V (A.translationMap g V p)
        exact (f.map_equivariant V _ p).symm) }
  map_id _ := RelativeInertiaHom.ext (by simp)
  map_comp _ _ := RelativeInertiaHom.ext (by simp)

end Inertia

namespace AbstractGroupQuotientStack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (G : Type w) [CommGroup G]
  [HasWeakSheafify (BigFppfOver.topology B S hS) GrpCat.{w}] (Y : Over S) (a : G →* Aut Y)

/-- **Stacks 0374.** The morphism `∐_{g ∈ G} [Y^g/G] → I_{[Y/G]}` of the source, assembled
from its summands. On `T`-points it is the source's recipe: a `G`-torsor `P → T` with a
`G`-equivariant `ψ : P → Y^g` is sent to `(P, ι ∘ ψ, α)` with `α` multiplication by `g`. -/
@[stacks 0374 "the morphism from the disjoint union of the [X^g/G] to the inertia stack"]
def inertiaComparison :
    (Σ g : G, fixedSchemeQuotient.{t} B S hS G Y a g) ⥤
      AbsoluteInertia (schemeQuotientProjection.{t} B S hS G Y a) :=
  Sigma.desc (fixedQuotientToInertia.{t} B S hS G Y a)

/-- The `g`-th summand of the comparison morphism is the functor
`[Y^g/G] ⥤ I_{[Y/G]}` of `AlgebraicGeometry.fixedQuotientToInertia`. -/
lemma inertiaComparison_incl (g : G) :
    Sigma.incl g ⋙ inertiaComparison.{t} B S hS G Y a =
      fixedQuotientToInertia.{t} B S hS G Y a g :=
  rfl

/-- **Stacks 0374.** The comparison morphism is a morphism *over* `(Sch/S)_fppf`: on each
summand, composing it with the structure functor of the inertia gives back the projection of
`[Y^g/G]` to the site, since neither the inclusion `Y^g → Y` nor remembering the
automorphism `α` changes the object of the site attached to a triple. -/
@[stacks 0374 "the comparison is a morphism over the big fppf site"]
lemma inertiaComparison_comp_struct (g : G) :
    Sigma.incl g ⋙ inertiaComparison.{t} B S hS G Y a ⋙
        relativeInertiaStruct (schemeQuotientProjection.{t} B S hS G Y a)
          (schemeQuotientProjection.{t} B S hS G Y a) =
      schemeQuotientProjection.{t} B S hS G (fixedScheme S G Y a g)
        (fixedSchemeAut Y a g) :=
  rfl

end AbstractGroupQuotientStack

end AlgebraicGeometry

end
