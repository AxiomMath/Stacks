module

public import StacksCore.CategoryTheory.Inertia
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.AbstractGroupQuotientInertia
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.AbstractGroupQuotientStack
public import Mathlib.CategoryTheory.Sigma.Basic

/-!
# The inertia stack of the quotient by a commutative group (Stacks 0374)

Let `S` be a scheme of a big fppf site `B`, let `G` be a *commutative* group, let `X` be a
sheaf on `(Sch/S)_fppf` and let `ρ : G →* Aut X` be an action of `G` on `X`. Stacks 0374
computes the inertia stack of the quotient `[[X/G]]` of Stacks 0371:
`I_{[X/G]} = ∐_{g ∈ G} [X^g/G]`, where `X^g` is the fixed locus of `g`, which the source
writes as the fibre product `X^g = X ×_{(1,1), X ×_S X, (g,1)} X`.

This file constructs that decomposition. The object `[X^g/G]` is the quotient of Stacks
0371 applied to `X^g`, so the summands of the formula live in exactly the same vocabulary
as `[[X/G]]` itself, and `I_{[X/G]}` is `CategoryTheory.AbsoluteInertia` of the projection
`[[X/G]] ⥤ (Sch/S)_fppf`.

## Main definitions

* `AlgebraicGeometry.fixedPresheaf`: the fixed subpresheaf `X^g` of an endomorphism of `X`,
  together with its inclusion `AlgebraicGeometry.fixedPresheafIncl` and the universal map
  `AlgebraicGeometry.fixedPresheafLift`.
* `AlgebraicGeometry.fixedPresheafAction`: the action of `G` on `X^g` induced by `ρ`, which
  exists because `G` is commutative.
* `AlgebraicGeometry.fixedQuotientStack`: the summand `[X^g/G]`, namely
  `AlgebraicGeometry.AbstractGroupQuotientStack` of `X^g` with that action.
* `AlgebraicGeometry.IsTranslationBy`: the property of an object of `I_{[X/G]}` that its
  automorphism is translation by the constant `g`; this cuts out the `g`-summand.
* `AlgebraicGeometry.inertiaSummand`: the canonical functor `[X^g/G] ⥤ I_{[X/G]}`, landing
  in the `g`-summand, and `AlgebraicGeometry.inertiaCoproduct`, their coproduct
  `∐_{g ∈ G} [X^g/G] ⥤ I_{[X/G]}`.

## Main results

* `AlgebraicGeometry.isPullback_fixedPresheaf`: `X^g` is the displayed fibre product
  `X ×_{(1,1), X ×_S X, (g,1)} X`. In presheaves on `(Sch/S)_fppf` the binary product *is*
  the fibre product over `S`, since `S` is the terminal object of the site.
* `AlgebraicGeometry.inertiaSummandLift_isEquivalence`: **Stacks 0374.** For each `g`, the
  canonical functor is an *equivalence* from `[X^g/G]` onto the full subcategory of
  `I_{[X/G]}` on the objects whose automorphism is translation by `g`: the `g`-summand of
  the formula is `[X^g/G]`. By `AlgebraicGeometry.inertiaSummandLift_comp_structure` it is
  an equivalence over `(Sch/S)_fppf`, and by
  `AlgebraicGeometry.incl_comp_inertiaCoproduct_comp_structure` the coproduct of these
  functors is a functor over `(Sch/S)_fppf` as well.
* `AlgebraicGeometry.existsUnique_auto_eq_totalSmul`: **Stacks 0374.** Conversely, the
  automorphism of an object of `I_{[X/G]}` is, at every point of the total space of its
  torsor, translation by a *unique* section of the constant sheaf of groups; and by
  `AlgebraicGeometry.exists_covering_nonempty_total` such points exist locally in the fppf
  topology. This is the source's "`α` is, locally in the fppf topology over `T`, given by
  multiplication by some element `g` of `G`".
  `AlgebraicGeometry.constantSheafOfGroupsUnit_eq_of_isTranslationBy` records that the
  labels are determined, so that distinct summands do not overlap.

## Implementation notes

The source's `X^g = {x ∈ X | g(x) = x}` is realized as the subpresheaf of sections fixed by
`ρ g`, and `AlgebraicGeometry.isPullback_fixedPresheaf` checks that this is the displayed
fibre product. Commutativity of `G` enters twice: it is what makes `X^g` stable under the
action of `G` (`AlgebraicGeometry.fixedPresheafAction`), and it is what makes translation by
a constant `g` an *equivariant* automorphism of a torsor
(`CategoryTheory.constantSheafOfGroupsUnit_central`), which is why the summands are indexed
by `G` at all.

Translation by a constant `g ∈ G` on the torsor of an object of `[[X/G]]` is taken from
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.AbstractGroupQuotientInertia`:
`AlgebraicGeometry.AbstractGroupQuotientStack.translationMap` on total spaces,
`AlgebraicGeometry.AbstractGroupQuotientStack.translationHom` as an endomorphism of an
object of `[[X/G]]` and
`AlgebraicGeometry.AbstractGroupQuotientStack.translation` as an automorphism of it. That
module treats the quotient of a *scheme* over `S` and this one the quotient of a *sheaf*,
but the automorphism `α` of the source is the same construction in both, so it is shared
rather than repeated.

The functor `AlgebraicGeometry.inertiaCoproduct` is defined on the categorical disjoint union
`CategoryTheory.Sigma.desc`, which is not itself equivalent to `I_{[X/G]}`; the coproduct of the
formula is the coproduct of stacks, and the equivalence of Stacks 0374 is
`AlgebraicGeometry.inertia_equivalence_stackCoproduct`, proved in
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.AbstractGroupQuotientInertiaEquivalence`. What is
proved here is the summand-by-summand identification together with the local statement that
exhausts `I_{[X/G]}`.

## References

* [Stacks Project, Tag 0374](https://stacks.math.columbia.edu/tag/0374)
* [Stacks Project, Tag 0371](https://stacks.math.columbia.edu/tag/0371)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite CategoryTheory.Limits

universe t z w u v

namespace AlgebraicGeometry

section FixedPresheaf

variable {C : Type u} [Category.{v} C] {X : Cᵒᵖ ⥤ Type z}

/-- Equal morphisms of presheaves of types agree on sections. -/
lemma presheafHom_congr_apply {Y Z : Cᵒᵖ ⥤ Type z} {a b : Y ⟶ Z} (h : a = b) (V : Cᵒᵖ)
    (y : Y.obj V) : a.app V y = b.app V y := by rw [h]

/-- The subpresheaf of sections fixed by an endomorphism `σ` of a presheaf of types. For
`σ = ρ g` this is the fixed locus `X^g = {x ∈ X | g(x) = x}` of Stacks 0374. -/
def fixedPresheaf (σ : X ⟶ X) : Cᵒᵖ ⥤ Type z where
  obj V := {x : X.obj V // σ.app V x = x}
  map f := TypeCat.ofHom fun x => ⟨X.map f x.1, by rw [NatTrans.naturality_apply, x.2]⟩
  map_id V := by ext x; simp
  map_comp f g := by ext x; simp

/-- The inclusion `X^σ → X` of the fixed subpresheaf. -/
def fixedPresheafIncl (σ : X ⟶ X) : fixedPresheaf σ ⟶ X where
  app V := TypeCat.ofHom fun (x : {x : X.obj V // σ.app V x = x}) => x.1
  naturality V W f := by ext x; rfl

/-- A section of `X` fixed by `σ`, read as a section of the fixed subpresheaf. -/
def fixedPresheafMk (σ : X ⟶ X) {V : Cᵒᵖ} (x : X.obj V) (hx : σ.app V x = x) :
    (fixedPresheaf σ).obj V := ⟨x, hx⟩

/-- The inclusion sends `fixedPresheafMk σ x hx` to `x`. -/
@[simp] lemma fixedPresheafIncl_app_mk (σ : X ⟶ X) {V : Cᵒᵖ} (x : X.obj V)
    (hx : σ.app V x = x) : (fixedPresheafIncl σ).app V (fixedPresheafMk σ x hx) = x := rfl

/-- The inclusion of the fixed subpresheaf is injective on sections. -/
lemma fixedPresheafIncl_app_injective (σ : X ⟶ X) (V : Cᵒᵖ) :
    Function.Injective ((fixedPresheafIncl σ).app V) :=
  fun _ _ h => Subtype.ext h

/-- Two sections of the fixed subpresheaf with the same image in `X` are equal. -/
lemma fixedPresheaf_ext (σ : X ⟶ X) {V : Cᵒᵖ} {y y' : (fixedPresheaf σ).obj V}
    (h : (fixedPresheafIncl σ).app V y = (fixedPresheafIncl σ).app V y') : y = y' :=
  fixedPresheafIncl_app_injective σ V h

/-- The image in `X` of a section of the fixed subpresheaf is fixed by `σ`. -/
@[simp] lemma fixedPresheaf_app_spec (σ : X ⟶ X) {V : Cᵒᵖ} (y : (fixedPresheaf σ).obj V) :
    σ.app V ((fixedPresheafIncl σ).app V y) = (fixedPresheafIncl σ).app V y :=
  y.2

/-- The inclusion of the fixed subpresheaf commutes with restriction of sections. -/
@[simp] lemma fixedPresheafIncl_app_map (σ : X ⟶ X) {V W : Cᵒᵖ} (f : V ⟶ W)
    (y : (fixedPresheaf σ).obj V) :
    (fixedPresheafIncl σ).app W ((fixedPresheaf σ).map f y) =
      X.map f ((fixedPresheafIncl σ).app V y) := rfl

/-- The inclusion of the fixed subpresheaf followed by `σ` is the inclusion. -/
@[simp] lemma fixedPresheafIncl_comp (σ : X ⟶ X) :
    fixedPresheafIncl σ ≫ σ = fixedPresheafIncl σ := by
  ext V y
  exact fixedPresheaf_app_spec σ y

/-- A map to `X` whose image is fixed by `σ` factors through the fixed subpresheaf. -/
def fixedPresheafLift (σ : X ⟶ X) {Y : Cᵒᵖ ⥤ Type z} (h : Y ⟶ X) (hh : h ≫ σ = h) :
    Y ⟶ fixedPresheaf σ where
  app V := TypeCat.ofHom fun y => fixedPresheafMk σ (h.app V y)
    (presheafHom_congr_apply hh V y)
  naturality V W f := by
    ext y
    exact fixedPresheaf_ext σ (by simp)

/-- The map `fixedPresheafLift σ h hh` followed by the inclusion is `h`. -/
@[simp] lemma fixedPresheafLift_comp_incl (σ : X ⟶ X) {Y : Cᵒᵖ ⥤ Type z} (h : Y ⟶ X)
    (hh : h ≫ σ = h) : fixedPresheafLift σ h hh ≫ fixedPresheafIncl σ = h := by
  ext V y
  rfl

/-- Two maps to the fixed subpresheaf that agree after the inclusion are equal. -/
lemma fixedPresheafIncl_mono (σ : X ⟶ X) {Y : Cᵒᵖ ⥤ Type z} {a b : Y ⟶ fixedPresheaf σ}
    (h : a ≫ fixedPresheafIncl σ = b ≫ fixedPresheafIncl σ) : a = b := by
  ext V y
  exact fixedPresheaf_ext σ (presheafHom_congr_apply h V y)

/-- **Stacks 0374.** The fixed subpresheaf `X^σ` is the fibre product
`X ×_{(1,1), X × X, (σ,1)} X` displayed in the source. On presheaves over the big fppf site
of `S` the binary product is the fibre product over `S`, as `S` is the terminal object. -/
@[stacks 0374 "the fixed locus as a fibre product"]
theorem isPullback_fixedPresheaf (σ : X ⟶ X) :
    IsPullback (fixedPresheafIncl σ) (fixedPresheafIncl σ)
      (prod.lift (𝟙 X) (𝟙 X)) (prod.lift σ (𝟙 X)) := by
  refine ⟨⟨by ext <;> simp⟩, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · refine fun s => fixedPresheafLift σ s.snd ?_
    have H₁ := congrArg (fun k => k ≫ (prod.fst : X ⨯ X ⟶ X)) s.condition
    have H₂ := congrArg (fun k => k ≫ (prod.snd : X ⨯ X ⟶ X)) s.condition
    simp only [Category.assoc, prod.lift_fst, prod.lift_snd, Category.comp_id] at H₁ H₂
    exact H₁.symm.trans H₂
  · intro s
    simpa using (congrArg (fun k => k ≫ (prod.snd : X ⨯ X ⟶ X)) s.condition).symm
  · intro s
    simp
  · intro s m _ hm
    exact fixedPresheafIncl_mono σ (by simpa using hm)

end FixedPresheaf

section FixedAction

variable {C : Type u} [Category.{v} C] {X : Cᵒᵖ ⥤ Type z}

/-- Commuting endomorphisms of a presheaf of types commute on every section. -/
lemma fixedPresheaf_commute_apply {σ τ : X ⟶ X} (hc : τ ≫ σ = σ ≫ τ) (V : Cᵒᵖ)
    (x : X.obj V) : σ.app V (τ.app V x) = τ.app V (σ.app V x) :=
  presheafHom_congr_apply hc V x

/-- An endomorphism `τ` commuting with `σ` restricts to the `σ`-fixed subpresheaf. -/
def fixedPresheafMap (σ τ : X ⟶ X) (hc : τ ≫ σ = σ ≫ τ) :
    fixedPresheaf σ ⟶ fixedPresheaf σ where
  app V := TypeCat.ofHom fun y => fixedPresheafMk σ (τ.app V ((fixedPresheafIncl σ).app V y))
    (by rw [fixedPresheaf_commute_apply hc, fixedPresheaf_app_spec])
  naturality V W f := by
    ext y
    exact fixedPresheaf_ext σ (by simp)

/-- On sections, the restriction `fixedPresheafMap σ τ hc` acts as `τ`. -/
@[simp] lemma fixedPresheafIncl_app_fixedPresheafMap (σ τ : X ⟶ X) (hc : τ ≫ σ = σ ≫ τ)
    (V : Cᵒᵖ) (y : (fixedPresheaf σ).obj V) :
    (fixedPresheafIncl σ).app V ((fixedPresheafMap σ τ hc).app V y) =
      τ.app V ((fixedPresheafIncl σ).app V y) := rfl

/-- The restriction to the `σ`-fixed subpresheaf of an automorphism commuting with `σ`. -/
def fixedPresheafAut (σ : X ⟶ X) (τ : Aut X) (hc : τ.hom ≫ σ = σ ≫ τ.hom) :
    Aut (fixedPresheaf σ) where
  hom := fixedPresheafMap σ τ.hom hc
  inv := fixedPresheafMap σ τ.inv (by
    have hhi : τ.hom ≫ τ.inv = 𝟙 X := τ.hom_inv_id
    have hih : τ.inv ≫ τ.hom = 𝟙 X := τ.inv_hom_id
    calc τ.inv ≫ σ = τ.inv ≫ (σ ≫ τ.hom) ≫ τ.inv := by
          rw [Category.assoc, hhi, Category.comp_id]
      _ = τ.inv ≫ (τ.hom ≫ σ) ≫ τ.inv := by rw [hc]
      _ = (τ.inv ≫ τ.hom) ≫ σ ≫ τ.inv := by simp
      _ = σ ≫ τ.inv := by rw [hih, Category.id_comp])
  hom_inv_id := by
    ext V y
    exact fixedPresheaf_ext σ (by
      simpa using presheafHom_congr_apply τ.hom_inv_id V ((fixedPresheafIncl σ).app V y))
  inv_hom_id := by
    ext V y
    exact fixedPresheaf_ext σ (by
      simpa using presheafHom_congr_apply τ.inv_hom_id V ((fixedPresheafIncl σ).app V y))

/-- On sections, the restricted automorphism `fixedPresheafAut σ τ hc` acts as `τ`. -/
@[simp] lemma fixedPresheafIncl_app_fixedPresheafAut (σ : X ⟶ X) (τ : Aut X)
    (hc : τ.hom ≫ σ = σ ≫ τ.hom) (V : Cᵒᵖ) (y : (fixedPresheaf σ).obj V) :
    (fixedPresheafIncl σ).app V ((fixedPresheafAut σ τ hc).hom.app V y) =
      τ.hom.app V ((fixedPresheafIncl σ).app V y) := rfl

variable {G : Type w} [CommGroup G]

/-- The automorphisms in the image of an action of a commutative group commute. -/
lemma commute_action_hom (ρ : G →* Aut X) (g h : G) :
    (ρ h).hom ≫ (ρ g).hom = (ρ g).hom ≫ (ρ h).hom :=
  congrArg Iso.hom (by rw [← map_mul, ← map_mul, mul_comm] : ρ g * ρ h = ρ h * ρ g)

/-- **Stacks 0374.** Because `G` is commutative, its action on `X` restricts to an action
on the fixed locus `X^g`. This is what makes the quotient `[X^g/G]` of the source's formula
meaningful. -/
@[stacks 0374 "the induced action on the fixed locus"]
def fixedPresheafAction (ρ : G →* Aut X) (g : G) : G →* Aut (fixedPresheaf (ρ g).hom) where
  toFun h := fixedPresheafAut (ρ g).hom (ρ h) (commute_action_hom ρ g h)
  map_one' := by
    refine Aut.ext ?_
    ext V y
    refine fixedPresheaf_ext _ ?_
    change (ρ (1 : G)).hom.app V ((fixedPresheafIncl (ρ g).hom).app V y) =
      (fixedPresheafIncl (ρ g).hom).app V y
    rw [map_one]
    rfl
  map_mul' h₁ h₂ := by
    refine Aut.ext ?_
    ext V y
    refine fixedPresheaf_ext _ ?_
    change (ρ (h₁ * h₂)).hom.app V ((fixedPresheafIncl (ρ g).hom).app V y) =
      (ρ h₁).hom.app V ((ρ h₂).hom.app V ((fixedPresheafIncl (ρ g).hom).app V y))
    rw [map_mul]
    rfl

/-- On sections of `X^g`, the induced action of `h` acts as `ρ h`. -/
@[simp] lemma fixedPresheafIncl_app_fixedPresheafAction (ρ : G →* Aut X) (g h : G) (V : Cᵒᵖ)
    (y : (fixedPresheaf (ρ g).hom).obj V) :
    (fixedPresheafIncl (ρ g).hom).app V ((fixedPresheafAction ρ g h).hom.app V y) =
      (ρ h).hom.app V ((fixedPresheafIncl (ρ g).hom).app V y) := rfl

/-- The inclusion of the fixed locus is equivariant for the induced action. -/
lemma fixedPresheafIncl_equivariant (ρ : G →* Aut X) (g h : G) :
    (fixedPresheafAction ρ g h).hom ≫ fixedPresheafIncl (ρ g).hom =
      fixedPresheafIncl (ρ g).hom ≫ (ρ h).hom := by
  ext V y
  rfl

/-- The induced action on the fixed locus is the unique one for which the inclusion is
equivariant, since the inclusion is a monomorphism. -/
lemma fixedPresheafAction_unique (ρ : G →* Aut X) (g : G)
    (b : G →* Aut (fixedPresheaf (ρ g).hom))
    (hb : ∀ h : G, (b h).hom ≫ fixedPresheafIncl (ρ g).hom =
      fixedPresheafIncl (ρ g).hom ≫ (ρ h).hom) : b = fixedPresheafAction ρ g := by
  refine MonoidHom.ext fun h => Aut.ext ?_
  refine fixedPresheafIncl_mono (ρ g).hom ?_
  rw [hb h, fixedPresheafIncl_equivariant]

end FixedAction

section Quotient

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (G : Type w) [CommGroup G]
  [HasWeakSheafify (BigFppfOver.topology B S hS) GrpCat.{w}]
  (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type z) (ρ : G →* Aut X)

namespace AbstractGroupQuotientStack

variable {B S hS G X ρ}

/-- Two sections of a torsor over the same object of the site that agree as elements of the
total space are equal. -/
lemma total_snd_eq {A : AbstractGroupQuotientStack.{t} B S hS G X ρ}
    {V : (BigFppfOver B S hS)ᵒᵖ} {a : V.unop ⟶ A.base}
    {x y : A.torsor.presheaf.obj (op (Over.mk a))} (h : (⟨a, x⟩ : A.Total V) = ⟨a, y⟩) :
    x = y :=
  eq_of_heq (Eq.mp (Sigma.mk.injEq
    (β := fun b : V.unop ⟶ A.base => A.torsor.presheaf.obj (op (Over.mk b))) a x a y) h).2

/-- Two sections of the total space of a torsor lying over the same morphism differ by a
unique section of the constant sheaf of groups: the torsor condition (PT) of Stacks 03AH. -/
lemma existsUnique_totalSmul_eq (A : AbstractGroupQuotientStack.{t} B S hS G X ρ)
    {V : (BigFppfOver B S hS)ᵒᵖ} (p q : A.Total V) (h : q.1 = p.1) :
    ∃! γ : (constantSheafOfGroups (BigFppfOver.topology B S hS) G).presheaf.obj V,
      A.totalSmul γ p = q := by
  obtain ⟨pa, ps⟩ := p
  obtain ⟨qa, qs⟩ := q
  subst h
  obtain ⟨γ, hγ, hu⟩ := A.torsor.simplyTransitive (op (Over.mk qa)) ⟨qs⟩ ps qs
  refine ⟨γ, Sigma.ext rfl (heq_of_eq hγ), fun δ hδ => hu δ ?_⟩
  exact total_snd_eq (A := A) (a := qa)
    (x := A.torsor.act (op (Over.mk qa)) δ ps) (y := qs) hδ

/-- Translating the torsor by a constant element of `G` acts on the equivariant map through
`ρ g`. -/
lemma totalToTarget_translationMap (A : AbstractGroupQuotientStack.{t} B S hS G X ρ) (g : G)
    (V : (BigFppfOver B S hS)ᵒᵖ) (p : A.Total V) :
    A.totalToTarget V (A.translationMap g V p) = (ρ g).hom.app V (A.totalToTarget V p) :=
  A.toTarget_equivariant (op (Over.mk p.1)) g p.2

end AbstractGroupQuotientStack

/-- **Stacks 0374.** The quotient `[X^g/G]` of the fixed locus `X^g` by `G`, formed by the
construction of Stacks 0371 applied to `X^g` with its induced action. -/
@[stacks 0374 "the quotient of the fixed locus"]
abbrev fixedQuotientStack (g : G) : Type _ :=
  AbstractGroupQuotientStack B S hS G (fixedPresheaf (ρ g).hom) (fixedPresheafAction ρ g)

/-- `I_{[X/G]}`, the inertia stack of `[[X/G]]`. -/
abbrev quotientInertia : Type _ :=
  AbsoluteInertia (AbstractGroupQuotientStack.projection (B := B) (S := S) (hS := hS)
    (G := G) (X := X) (ρ := ρ))

variable {B S hS G X ρ}

/-- An object of `[X^g/G]`, pushed along the inclusion `X^g → X` to an object of
`[[X/G]]`: the torsor is unchanged and the equivariant map is composed with `X^g → X`. -/
def fixedPush {g : G} (A : fixedQuotientStack B S hS G X ρ g) :
    AbstractGroupQuotientStack B S hS G X ρ where
  base := A.base
  torsor := A.torsor
  isTorsor := A.isTorsor
  toTarget W s := (fixedPresheafIncl (ρ g).hom).app (op W.unop.left) (A.toTarget W s)
  toTarget_naturality h s := by
    rw [A.toTarget_naturality h s]
    rfl
  toTarget_equivariant W h s := by
    rw [A.toTarget_equivariant W h s]
    rfl

/-- The values of the equivariant map of a pushed object are fixed by `ρ g`. -/
lemma rho_fix_fixedPush {g : G} (A : fixedQuotientStack B S hS G X ρ g)
    (V : (BigFppfOver B S hS)ᵒᵖ) (p : (fixedPush A).Total V) :
    (ρ g).hom.app V ((fixedPush A).totalToTarget V p) = (fixedPush A).totalToTarget V p :=
  fixedPresheaf_app_spec (ρ g).hom (A.toTarget (op (Over.mk p.1)) p.2)

/-- A morphism of `[X^g/G]`, pushed to a morphism of `[[X/G]]`. -/
def fixedPushMap {g : G} {A A' : fixedQuotientStack B S hS G X ρ g} (m : A ⟶ A') :
    fixedPush A ⟶ fixedPush A' where
  base := m.base
  map := m.map
  map_naturality := m.map_naturality
  map_equivariant := m.map_equivariant
  bijOn_map := m.bijOn_map
  totalToTarget_comp V p :=
    congrArg ((fixedPresheafIncl (ρ g).hom).app V) (m.totalToTarget_comp V p)

/-- The property of an object of `I_{[X/G]}` that its automorphism is translation by the
constant `g ∈ G`. This is the `g`-summand of the formula of Stacks 0374. -/
def IsTranslationBy (g : G) : ObjectProperty (quotientInertia B S hS G X ρ) :=
  fun Z => ∀ (V : (BigFppfOver B S hS)ᵒᵖ) (p : Z.obj.Total V),
    Z.auto.hom.map V p = Z.obj.translationMap g V p

/-- **Stacks 0374.** The canonical functor `[X^g/G] ⥤ I_{[X/G]}`: a torsor with an
equivariant map to `X^g` is sent to the same torsor, mapping to `X`, together with the
automorphism given by translation by `g`. -/
@[stacks 0374 "the canonical functor to the inertia stack"]
def inertiaSummand (g : G) :
    fixedQuotientStack B S hS G X ρ g ⥤ quotientInertia B S hS G X ρ where
  obj A :=
    { obj := fixedPush A
      auto := AbstractGroupQuotientStack.translation g (rho_fix_fixedPush A)
      cond := rfl }
  map {A A'} m :=
    { hom := fixedPushMap m
      comm := AbstractGroupQuotientStack.Hom.ext
        ((Category.comp_id _).trans (Category.id_comp _).symm) (by
        funext V p
        exact (m.map_equivariant V _ p).symm) }
  map_id A := RelativeInertiaHom.ext rfl
  map_comp m m' := RelativeInertiaHom.ext rfl

/-- The image of an object under `inertiaSummand g` has automorphism translation by `g`. -/
lemma isTranslationBy_inertiaSummand_obj (g : G)
    (A : fixedQuotientStack B S hS G X ρ g) :
    IsTranslationBy g ((inertiaSummand g).obj A) := fun _ _ => rfl

/-- The functor of Stacks 0374 lands in the `g`-summand. -/
def inertiaSummandLift (g : G) :
    fixedQuotientStack B S hS G X ρ g ⥤
      (IsTranslationBy (ρ := ρ) g).FullSubcategory :=
  ObjectProperty.lift _ (inertiaSummand g) (isTranslationBy_inertiaSummand_obj g)

/-- **Stacks 0374.** Conversely, if the automorphism of an object of `I_{[X/G]}` is
translation by the constant `g`, then the condition `φ ∘ α = φ` says exactly that its
equivariant map factors through the inclusion of the fixed locus `X^g` in `X`; this is the
resulting object of `[X^g/G]`. -/
def fixedPull {g : G} (Z : quotientInertia B S hS G X ρ) (hZ : IsTranslationBy g Z) :
    fixedQuotientStack B S hS G X ρ g where
  base := Z.obj.base
  torsor := Z.obj.torsor
  isTorsor := Z.obj.isTorsor
  toTarget W s := fixedPresheafMk (ρ g).hom (Z.obj.toTarget W s) (by
    have h1 := Z.auto.hom.totalToTarget_comp (op W.unop.left)
      (⟨W.unop.hom, s⟩ : Z.obj.Total (op W.unop.left))
    rw [hZ (op W.unop.left) (⟨W.unop.hom, s⟩ : Z.obj.Total (op W.unop.left))] at h1
    exact (Z.obj.totalToTarget_translationMap g (op W.unop.left)
      (⟨W.unop.hom, s⟩ : Z.obj.Total (op W.unop.left))).symm.trans h1)
  toTarget_naturality h s := fixedPresheaf_ext _ (Z.obj.toTarget_naturality h s)
  toTarget_equivariant W h s := fixedPresheaf_ext _ (Z.obj.toTarget_equivariant W h s)

/-- The automorphism of an object of the `g`-summand is the translation automorphism of the
object of `[X^g/G]` it comes from. -/
lemma translationHom_fixedPull {g : G} (Z : quotientInertia B S hS G X ρ)
    (hZ : IsTranslationBy g Z) :
    AbstractGroupQuotientStack.translationHom (A := fixedPush (fixedPull Z hZ)) g
        (rho_fix_fixedPush _) = Z.auto.hom :=
  AbstractGroupQuotientStack.Hom.ext Z.cond.symm (funext fun V => funext fun p => (hZ V p).symm)

/-- **Stacks 0374.** An object of the `g`-summand of `I_{[X/G]}` is the image of the object
of `[X^g/G]` underlying it. -/
def inertiaSummandObjIso {g : G} (Z : quotientInertia B S hS G X ρ)
    (hZ : IsTranslationBy g Z) : (inertiaSummand g).obj (fixedPull Z hZ) ≅ Z where
  hom :=
    { hom := 𝟙 Z.obj
      comm := (Category.id_comp _).trans
        ((translationHom_fixedPull Z hZ).symm.trans (Category.comp_id _).symm) }
  inv :=
    { hom := 𝟙 Z.obj
      comm := (Category.id_comp _).trans
        ((translationHom_fixedPull Z hZ).trans (Category.comp_id _).symm) }
  hom_inv_id := RelativeInertiaHom.ext (Category.id_comp _)
  inv_hom_id := RelativeInertiaHom.ext (Category.id_comp _)

/-- The functor `inertiaSummand g` is faithful. -/
instance inertiaSummand_faithful (g : G) : (inertiaSummand (ρ := ρ) g).Faithful where
  map_injective {_ _ m m'} h := by
    have h1 : fixedPushMap m = fixedPushMap m' := congrArg RelativeInertiaHom.hom h
    exact AbstractGroupQuotientStack.Hom.ext (congrArg (fun k => k.base) h1)
      (congrArg (fun k => k.map) h1)

/-- The functor `inertiaSummand g` is full. -/
instance inertiaSummand_full (g : G) : (inertiaSummand (ρ := ρ) g).Full where
  map_surjective {_ _} f :=
    ⟨{ base := f.hom.base
       map := f.hom.map
       map_naturality := f.hom.map_naturality
       map_equivariant := f.hom.map_equivariant
       bijOn_map := f.hom.bijOn_map
       totalToTarget_comp := fun V p =>
         fixedPresheaf_ext _ (f.hom.totalToTarget_comp V p) },
     RelativeInertiaHom.ext rfl⟩

/-- The functor `inertiaSummandLift g` is faithful. -/
instance inertiaSummandLift_faithful (g : G) : (inertiaSummandLift (ρ := ρ) g).Faithful :=
  (inferInstance : (ObjectProperty.lift (IsTranslationBy (ρ := ρ) g) (inertiaSummand g)
    (isTranslationBy_inertiaSummand_obj g)).Faithful)

/-- The functor `inertiaSummandLift g` is full. -/
instance inertiaSummandLift_full (g : G) : (inertiaSummandLift (ρ := ρ) g).Full :=
  (inferInstance : (ObjectProperty.lift (IsTranslationBy (ρ := ρ) g) (inertiaSummand g)
    (isTranslationBy_inertiaSummand_obj g)).Full)

/-- The functor `inertiaSummandLift g` is essentially surjective. -/
instance inertiaSummandLift_essSurj (g : G) : (inertiaSummandLift (ρ := ρ) g).EssSurj where
  mem_essImage Z :=
    ⟨fixedPull Z.obj Z.property,
      ⟨(ObjectProperty.fullyFaithfulι (IsTranslationBy (ρ := ρ) g)).preimageIso
        (inertiaSummandObjIso Z.obj Z.property)⟩⟩

/-- **Stacks 0374.** `I_{[X/G]} = ∐_{g ∈ G} [X^g/G]`, summand by summand: for each `g ∈ G`
the canonical functor is an equivalence from the quotient `[X^g/G]` of the fixed locus onto
the part of the inertia stack of `[[X/G]]` on which the automorphism is translation by `g`.
Objects correspond because `φ ∘ α = φ` says that `φ` factors through `X^g → X`, and
morphisms correspond because a morphism of `[[X/G]]` is `G`-equivariant. -/
@[stacks 0374 "the g-summand of the inertia stack"]
theorem inertiaSummandLift_isEquivalence (g : G) :
    (inertiaSummandLift (ρ := ρ) g).IsEquivalence where

/-- The equivalence of Stacks 0374 is an equivalence over `(Sch/S)_fppf`: it carries the
projection of `[X^g/G]` to the structure functor of the inertia stack. -/
@[stacks 0374 "the g-summand is an equivalence over the base"]
theorem inertiaSummandLift_comp_structure (g : G) :
    inertiaSummandLift (ρ := ρ) g ⋙ ObjectProperty.ι (IsTranslationBy (ρ := ρ) g) ⋙
        relativeInertiaStruct
          (AbstractGroupQuotientStack.projection (B := B) (S := S) (hS := hS) (G := G)
            (X := X) (ρ := ρ))
          (AbstractGroupQuotientStack.projection (B := B) (S := S) (hS := hS) (G := G)
            (X := X) (ρ := ρ)) =
      AbstractGroupQuotientStack.projection (B := B) (S := S) (hS := hS) (G := G)
        (X := fixedPresheaf (ρ g).hom) (ρ := fixedPresheafAction ρ g) :=
  rfl

/-- **Stacks 0374.** The disjoint union `∐_{g ∈ G} [X^g/G]` of the quotients of the fixed
loci, mapping to the inertia stack of `[[X/G]]`; on the `g`-summand this is
`AlgebraicGeometry.inertiaSummand`. -/
@[stacks 0374 "the disjoint union of the quotients of the fixed loci"]
def inertiaCoproduct :
    (Σ g : G, fixedQuotientStack B S hS G X ρ g) ⥤ quotientInertia B S hS G X ρ :=
  Sigma.desc inertiaSummand

/-- On the `g`-summand the coproduct of Stacks 0374 is the canonical functor. -/
@[simp] theorem incl_comp_inertiaCoproduct (g : G) :
    Sigma.incl g ⋙ inertiaCoproduct (ρ := ρ) = inertiaSummand g := rfl

/-- The coproduct of Stacks 0374 maps to the inertia stack over `(Sch/S)_fppf`: on each
summand it carries the projection of `[X^g/G]` to the structure functor of the inertia. -/
@[stacks 0374 "the coproduct over the base"]
theorem incl_comp_inertiaCoproduct_comp_structure (g : G) :
    Sigma.incl g ⋙ inertiaCoproduct (ρ := ρ) ⋙
        relativeInertiaStruct
          (AbstractGroupQuotientStack.projection (B := B) (S := S) (hS := hS) (G := G)
            (X := X) (ρ := ρ))
          (AbstractGroupQuotientStack.projection (B := B) (S := S) (hS := hS) (G := G)
            (X := X) (ρ := ρ)) =
      AbstractGroupQuotientStack.projection (B := B) (S := S) (hS := hS) (G := G)
        (X := fixedPresheaf (ρ g).hom) (ρ := fixedPresheafAction ρ g) :=
  rfl

/-- **Stacks 0374.** Conversely to `AlgebraicGeometry.inertiaSummand`: the automorphism `α`
of an object `(P/T, φ, α)` of `I_{[X/G]}` is, at every section of its torsor, translation by
a *unique* section of the constant sheaf of groups with value `G`. Commutativity of `G` is
not needed for this step; what it buys is that the section is independent of the chosen
point, which is why the summands of the formula are indexed by `G`. -/
@[stacks 0374 "the automorphism is a translation"]
theorem existsUnique_auto_eq_totalSmul (Z : quotientInertia B S hS G X ρ)
    (V : (BigFppfOver B S hS)ᵒᵖ) (p : Z.obj.Total V) :
    ∃! γ : (constantSheafOfGroups (BigFppfOver.topology B S hS) G).presheaf.obj V,
      Z.obj.totalSmul γ p = Z.auto.hom.map V p :=
  Z.obj.existsUnique_totalSmul_eq p (Z.auto.hom.map V p) (by
    rw [Z.auto.hom.fst_map p, show Z.auto.hom.base = 𝟙 Z.obj.base from Z.cond,
      Category.comp_id])

/-- **Stacks 0374.** The summands of the formula are distinguished by their labels: if the
automorphism of an object of `I_{[X/G]}` is translation by `g` and also by `h`, then `g` and
`h` have the same image in the constant sheaf of groups over every object carrying a point
of the total space of the torsor. -/
theorem constantSheafOfGroupsUnit_eq_of_isTranslationBy {g h : G}
    (Z : quotientInertia B S hS G X ρ) (hg : IsTranslationBy g Z) (hh : IsTranslationBy h Z)
    (V : (BigFppfOver B S hS)ᵒᵖ) (p : Z.obj.Total V) :
    constantSheafOfGroupsUnit (BigFppfOver.topology B S hS) G V g =
      constantSheafOfGroupsUnit (BigFppfOver.topology B S hS) G V h :=
  (existsUnique_auto_eq_totalSmul Z V p).unique (hg V p).symm (hh V p).symm

/-- **Stacks 0374.** The torsor of an object of `I_{[X/G]}` has points locally in the fppf
topology, so with `AlgebraicGeometry.existsUnique_auto_eq_totalSmul` the automorphism `α` is
locally a translation; this is the source's "`α` is, locally in the fppf topology over `T`,
given by multiplication by some element `g` of `G`". -/
theorem exists_covering_nonempty_total (Z : quotientInertia B S hS G X ρ)
    (U : Over Z.obj.base) :
    ∃ R ∈ ((BigFppfOver.topology B S hS).over Z.obj.base) U,
      ∀ ⦃W : Over Z.obj.base⦄ ⦃f : W ⟶ U⦄, R f → Nonempty (Z.obj.Total (op W.left)) := by
  obtain ⟨R, hR, hne⟩ := Z.obj.isTorsor U
  refine ⟨R, hR, ?_⟩
  intro W f hf
  exact (hne hf).map fun s => ⟨W.hom, s⟩

end Quotient

end AlgebraicGeometry

end
