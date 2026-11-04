module

public import Mathlib.CategoryTheory.Action.Limits
public import StacksFrontier.CategoryTheory.Sites.Point.SkyscraperStalkSplitting
public import StacksFrontier.CategoryTheory.Sites.Sheaf.ExampleOfGSets
import StacksCore.Tactic.StacksAttribute

/-!
# Skyscraper sheaves at the forgetful point of the site of `G`-sets

Let `G` be a monoid, let `𝒯_G` be the site of `G`-sets and let `p` be the point of `𝒯_G` whose
inverse image is the functor forgetting the `G`-action. Sheaves of sets on `𝒯_G` are `G`-sets,
the direct image along `p` of a set `E` is the `G`-set `Map(G, E)` with `g · ψ = ψ ∘ R_g`, and
the forgetful functor is left adjoint to `E ↦ Map(G, E)`. Consequently `p⁻¹p_*E = Map(G, E)`,
the counit `p⁻¹p_*E ⟶ E` is evaluation at `1_G`, its canonical section sends `m` to the
constant function with value `m`, and the kernel `I(E)` of the counit is the set of functions
vanishing at `1_G`. The stalk of a sheaf is its set of sections over an object presenting the
regular `G`-set `{}_G G`, so the stalk of the sheaf of rings attached to a commutative ring `R`
with a `G`-action is the ring of equivariant maps `{}_G G → R`, that is `R` with the action
forgotten.

## Main definitions

* `Stacks.Sites.GSets.coind`: the functor `E ↦ Map(G, E)` from sets to `G`-sets.
* `Stacks.Sites.GSets.forgetCoindAdj`: the adjunction between the forgetful functor and
  `E ↦ Map(G, E)`.
* `Stacks.Sites.GSets.forgetfulPoint`: the point of the topos of sheaves on `𝒯_G` whose inverse
  image is the forgetful functor.
* `Stacks.Sites.GSets.equivariantSubring`: the sections of the sheaf of rings attached to a ring
  with a `G`-action, the equivariant maps with their pointwise operations.

## Main results

* `Stacks.Sites.GSets.skyscraperStalkEquiv`: the identification `p⁻¹p_*E = Map(G, E)`.
* `Stacks.Sites.GSets.counit_app_eq_skyscraperStalkEquiv_one`: the counit is evaluation at
  `1_G`.
* `Stacks.Sites.GSets.skyscraperStalkEquiv_counitSection`: the canonical section of the counit
  sends `m` to the constant function with value `m`.
* `Stacks.Sites.GSets.kernelCounitEquiv`: the kernel of the counit is the group of functions
  vanishing at `1_G`.
* `Stacks.Sites.GSets.stalkEquivSectionsAtRegular` and
  `Stacks.Sites.GSets.sectionsAtRegularRingEquiv`: the stalk of the sheaf of rings attached to
  `R` is its ring of sections over an object presenting `{}_G G`, and evaluation at the base
  point identifies that ring with `R`.

## Implementation notes

The source's `𝒯_G` depends on set-theoretic choices, and enters here only through an
equivalence `e` between `G`-sets and its sheaves of sets, the equivalence supplied by
`CategoryTheory.Sites.Sheaf.Action.exists_equivalence_sheaf`; where the sections of the sheaf
attached to a `G`-set are needed, the equivalence is required to be restricted Yoneda, which is
how that result pins it. The point is built by transporting the adjunction between the
forgetful functor and `E ↦ Map(G, E)` along `e`, so its inverse image is the forgetful functor:
a point of a topos is determined by its inverse image, its direct image being the right
adjoint.

`p⁻¹p_*E = Map(G, E)` is stated for an arbitrary set `E` rather than only for the underlying
set of a module, and the kernel of the counit for an arbitrary abelian group object; the
`I(M)` of the source is the kernel of the counit by the definition preceding Tag 05V7.

The structure sheaf attached to `R` is presented by its sections: over an object `U` of the site
they are the equivariant maps `U → R`, a subring of all maps under the pointwise operations, and
`equivariantSubringEquivHom` identifies them with the sections over `U` of the sheaf of sets
attached to the `G`-set `R`, which is what it means for the sheaf of rings to correspond to `R`.
Its stalk at `p` is then its ring of sections over an object presenting `{}_G G`, so the ring
structure on the stalk is the one carried by those sections.

`G` is only required to be a monoid; the source states the example for a group. The universe of
`G`, of `R` and of the sheaves of sets must agree, since `{}_G G` has `G` as underlying set and
`Action.ofMulAction G R` has `R`; the objects and morphisms of the site stay in independent
universes.

## References

* [Stacks Project, Example 18.38.4 (Tag 05V9)](https://stacks.math.columbia.edu/tag/05V9)
* [Stacks Project, Example 7.33.7 (Tag 00YF)](https://stacks.math.columbia.edu/tag/00YF)
-/

@[expose] public section

namespace Stacks.Sites.GSets

open CategoryTheory CategoryTheory.Limits

universe w v u

variable (G : Type w) [Monoid G]

/-! ### The functor `E ↦ Map(G, E)` and its adjunction with the forgetful functor -/

/-- `Map(G, E)` as a `G`-set, with `g` acting by right translation of the argument:
`g · ψ = ψ ∘ R_g`. -/
abbrev coindObj (E : Type w) : Action (Type w) G where
  V := G → E
  ρ :=
    { toFun := fun g => ↾(fun ψ => fun h => ψ (h * g))
      map_one' := ConcreteCategory.hom_ext _ _ fun ψ => by
        change (fun h => ψ (h * 1)) = ψ
        simp
      map_mul' := fun g g' => ConcreteCategory.hom_ext _ _ fun ψ => by
        change (fun h => ψ (h * (g * g'))) = (fun h => ψ (h * g * g'))
        simp [mul_assoc] }

/-- In `Map(G, E)`, `(g · ψ)(h) = ψ(h * g)`. -/
@[simp] lemma coindObj_ρ_apply (E : Type w) (g h : G) (ψ : G → E) :
    ConcreteCategory.hom ((coindObj G E).ρ g) ψ h = ψ (h * g) := rfl

variable {G}

/-- Acting by a product is acting twice. -/
lemma ρ_mul_apply (X : Action (Type w) G) (g h : G) (x : X.V) :
    ConcreteCategory.hom (X.ρ (h * g)) x =
      ConcreteCategory.hom (X.ρ h) (ConcreteCategory.hom (X.ρ g) x) :=
  DFunLike.congr_fun (congrArg ConcreteCategory.hom (X.ρ.map_mul h g)) x

/-- A morphism of `G`-sets is equivariant. -/
lemma hom_ρ_apply {X Y : Action (Type w) G} (φ : X ⟶ Y) (g : G) (x : X.V) :
    ConcreteCategory.hom φ.hom (ConcreteCategory.hom (X.ρ g) x) =
      ConcreteCategory.hom (Y.ρ g) (ConcreteCategory.hom φ.hom x) :=
  DFunLike.congr_fun (congrArg ConcreteCategory.hom (φ.comm g)) x

variable (G)

/-- The functor `E ↦ Map(G, E)` from sets to `G`-sets, right adjoint to the forgetful
functor. -/
abbrev coind : Type w ⥤ Action (Type w) G where
  obj E := coindObj G E
  map f := { hom := ↾(fun ψ => fun g => f (ψ g)), comm := fun _ => rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The map `Map(G, E) → Map(G, E')` induced by `f : E → E'` is postcomposition with `f`. -/
@[simp] lemma coind_map_apply {E E' : Type w} (f : E ⟶ E') (ψ : G → E) (g : G) :
    ConcreteCategory.hom ((coind G).map f).hom ψ g = f (ψ g) := rfl

/-- The forgetful functor from `G`-sets to sets is left adjoint to `E ↦ Map(G, E)`:
an equivariant map `X → Map(G, E)` is the same thing as a map `X → E`, by evaluation at
`1_G`, the inverse sending `f` to `x ↦ (g ↦ f (g · x))`. -/
def forgetCoindAdj : Action.forget (Type w) G ⊣ coind G :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X E =>
        { toFun := fun f =>
            { hom := ↾(fun x => fun g => f (ConcreteCategory.hom (X.ρ g) x))
              comm := fun g => ConcreteCategory.hom_ext _ _ fun x => by
                change (fun h => f (ConcreteCategory.hom (X.ρ h)
                    (ConcreteCategory.hom (X.ρ g) x))) =
                  (fun h => f (ConcreteCategory.hom (X.ρ (h * g)) x))
                exact funext fun h => congrArg _ (ρ_mul_apply X g h x).symm }
          invFun := fun φ => ↾(fun x => ConcreteCategory.hom φ.hom x 1)
          left_inv := fun f => ConcreteCategory.hom_ext _ _ fun x => by
            change f (ConcreteCategory.hom (X.ρ 1) x) = f x
            rw [X.ρ_one]
            rfl
          right_inv := fun φ => Action.Hom.ext (ConcreteCategory.hom_ext _ _ fun x => by
            change (fun g => ConcreteCategory.hom φ.hom (ConcreteCategory.hom (X.ρ g) x) 1) =
              ConcreteCategory.hom φ.hom x
            refine funext fun g => ?_
            rw [hom_ρ_apply φ g x, coindObj_ρ_apply, one_mul]) }
      homEquiv_naturality_left_symm := fun _ _ => rfl
      homEquiv_naturality_right := fun _ _ => rfl }

/-- The counit of `forgetCoindAdj` at `E` is evaluation at `1_G`. -/
@[simp] lemma forgetCoindAdj_counit_app (E : Type w) (ψ : G → E) :
    (forgetCoindAdj G).counit.app E ψ = ψ 1 := rfl

/-! ### The forgetful point and the stalk of a skyscraper -/

section Point

variable {T : Type u} [Category.{v} T] {J : GrothendieckTopology T}
  (e : Action (Type w) G ≌ Sheaf J (Type w))

/-- The point of the topos of sheaves on the site of `G`-sets whose inverse image is the
functor forgetting the `G`-action: its direct image is `E ↦ Map(G, E)`. -/
def forgetfulPoint : PointOfTopos.{w, v, u} J where
  pushforward := coind G ⋙ e.functor
  inverseImage := e.inverse ⋙ Action.forget (Type w) G
  adj := e.symm.toAdjunction.comp (forgetCoindAdj G)
  preservesFiniteLimits :=
    have : PreservesFiniteLimits e.inverse := inferInstance
    have : PreservesFiniteLimits (Action.forget (Type w) G) := inferInstance
    comp_preservesFiniteLimits _ _

/-- The inverse image of `forgetfulPoint G e` is `e.inverse` followed by the forgetful
functor. -/
@[simp] lemma forgetfulPoint_inverseImage :
    (forgetfulPoint G e).inverseImage = e.inverse ⋙ Action.forget (Type w) G := rfl

/-- The direct image of `forgetfulPoint G e` is `E ↦ Map(G, E)` followed by `e.functor`. -/
@[simp] lemma forgetfulPoint_pushforward :
    (forgetfulPoint G e).pushforward = coind G ⋙ e.functor := rfl

/-- **Stacks Project, Tag 05V9.** The identification `p⁻¹p_*E = Map(G, E)`: the direct image of
`E` is the `G`-set `Map(G, E)` and the inverse image forgets the action. -/
@[stacks 05V9 "p⁻¹p_*M = Map(G, M)"]
def skyscraperStalkEquiv (E : Type w) :
    ((forgetfulPoint G e).pushforward ⋙ (forgetfulPoint G e).inverseImage).obj E ≃ (G → E) :=
  (((Action.forget (Type w) G).mapIso (e.unitIso.app (coindObj G E))).toEquiv).symm

/-- The identification of `p⁻¹p_*E` with `Map(G, E)` is natural in `E`. -/
lemma skyscraperStalkEquiv_naturality {E E' : Type w} (f : E ⟶ E')
    (x : ((forgetfulPoint G e).pushforward ⋙ (forgetfulPoint G e).inverseImage).obj E) (g : G) :
    skyscraperStalkEquiv G e E'
        (((forgetfulPoint G e).pushforward ⋙ (forgetfulPoint G e).inverseImage).map f x) g =
      f (skyscraperStalkEquiv G e E x g) :=
  congrFun (DFunLike.congr_fun (congrArg ConcreteCategory.hom
    (congrArg (Action.forget (Type w) G).map
      (e.unitIso.inv.naturality ((coind G).map f)))) x) g

/-- **Stacks Project, Tag 05V9.** Under the identification of `p⁻¹p_*E` with `Map(G, E)` the
counit `p⁻¹p_*E ⟶ E` is evaluation at `1_G`. -/
@[stacks 05V9 "the counit p⁻¹p_*M → M is evaluation at 1_G"]
theorem counit_app_eq_skyscraperStalkEquiv_one (E : Type w)
    (x : ((forgetfulPoint G e).pushforward ⋙ (forgetfulPoint G e).inverseImage).obj E) :
    (forgetfulPoint G e).adj.counit.app E x = skyscraperStalkEquiv G e E x 1 := rfl

/-- **Stacks Project, Tag 05V9.** Under the identification of `p⁻¹p_*E` with `Map(G, E)` the
canonical section of the counit sends `m` to the constant function with value `m`. -/
@[stacks 05V9 "M → Map(G, M) assigns to m the constant function with value m"]
theorem skyscraperStalkEquiv_counitSection (E : Type w) (m : E) :
    skyscraperStalkEquiv G e E ((forgetfulPoint G e).counitSection.app E m) =
      Function.const G m := by
  funext g
  show skyscraperStalkEquiv G e E
      (((forgetfulPoint G e).pushforward ⋙ (forgetfulPoint G e).inverseImage).map
        (↾fun (_ : PUnit.{w + 1}) => m) (forgetfulPoint G e).basePoint) g = m
  rw [skyscraperStalkEquiv_naturality]
  rfl

/-- **Stacks Project, Tag 05V9.** `I(M) = {f : G → M | f(1_G) = 0}`: the kernel of the counit at
an abelian group object `A` is the set of functions `G → A` vanishing at `1_G`. An abelian group
object is written multiplicatively, so its zero is denoted `1`. -/
@[stacks 05V9 "I(M) = {f : G → M | f(1_G) = 0}"]
def kernelCounitEquiv (A : CommGrp (Type w)) :
    {x : ((forgetfulPoint G e).pushforward ⋙ (forgetfulPoint G e).inverseImage).obj A.X //
        (forgetfulPoint G e).adj.counit.app A.X x =
          (1 : commGrpTypeEquivalenceCommGrp.functor.obj A)} ≃
      {f : G → A.X // f 1 = (1 : commGrpTypeEquivalenceCommGrp.functor.obj A)} :=
  Equiv.subtypeEquiv (skyscraperStalkEquiv G e A.X) fun x => by
    rw [counit_app_eq_skyscraperStalkEquiv_one]

end Point

/-! ### The stalk as the sections over the regular `G`-set -/

/-- A point of a `G`-set `S` is the same thing as an equivariant map from the left regular
`G`-set: the map `φ` corresponds to `φ(1_G)`. -/
def leftRegularHomEquiv (S : Action (Type w) G) : (Action.leftRegular G ⟶ S) ≃ S.V where
  toFun φ := ConcreteCategory.hom φ.hom (1 : G)
  invFun s :=
    { hom := ↾(fun g => ConcreteCategory.hom (S.ρ g) s)
      comm := fun g => ConcreteCategory.hom_ext _ _ fun x =>
        ρ_mul_apply S x g s }
  left_inv φ := Action.Hom.ext (ConcreteCategory.hom_ext _ _ fun g => by
    have h : ∀ x : G, ConcreteCategory.hom ((Action.leftRegular G).ρ x) (1 : G) = x :=
      fun x => mul_one x
    change ConcreteCategory.hom (S.ρ g) (ConcreteCategory.hom φ.hom (1 : G)) =
      ConcreteCategory.hom φ.hom g
    rw [← hom_ρ_apply φ g (1 : G)]
    exact congrArg _ (h g))
  right_inv s := by
    change ConcreteCategory.hom (S.ρ 1) s = s
    rw [S.ρ_one]
    rfl

section Regular

variable {T : Type u} [Category.{v} T] {ι : T ⥤ Action (Type w) G} {u₀ : T}
  (α : ι.obj u₀ ≅ Action.leftRegular G) {J : GrothendieckTopology T}
  (e : Action (Type w) G ≌ Sheaf J (Type w))
  (he : e.functor ⋙ sheafToPresheaf J (Type w) =
    yoneda ⋙ (Functor.whiskeringLeft Tᵒᵖ (Action (Type w) G)ᵒᵖ (Type w)).obj ι.op)

/-- The sections of the sheaf attached to a `G`-set `S` over an object `U` of the site are the
equivariant maps from `U` to `S`: this is what it means for the equivalence to be restricted
Yoneda. -/
def sectionsHomEquiv (S : Action (Type w) G) (U : T) :
    (e.functor.obj S).obj.obj (Opposite.op U) ≃ (ι.obj U ⟶ S) :=
  Equiv.cast (congrArg
    (fun F : Action (Type w) G ⥤ Tᵒᵖ ⥤ Type w => (F.obj S).obj (Opposite.op U)) he)

/-- The stalk at the forgetful point is the set of sections over an object presenting the
regular `G`-set: the stalk of `F` is the underlying set of the `G`-set `F`, which is the set of
its sections over `{}_G G`. -/
def stalkRegularEquiv (F : Sheaf J (Type w)) :
    (forgetfulPoint G e).inverseImage.obj F ≃ F.obj.obj (Opposite.op u₀) :=
  ((leftRegularHomEquiv G (e.inverse.obj F)).symm.trans
      (α.homCongr (Iso.refl (e.inverse.obj F))).symm).trans
    (((sectionsHomEquiv G e he (e.inverse.obj F) u₀).symm).trans
      (((sheafToPresheaf J (Type w)).mapIso (e.counitIso.app F)).app
        (Opposite.op u₀)).toEquiv)

end Regular

/-! ### The structure sheaf attached to a ring with a `G`-action -/

variable (R : Type w) [CommRing R] [MulSemiringAction G R]

/-- The equivariant maps from a `G`-set `X` to a commutative ring `R` with a `G`-action form a
subring of all maps `X → R` under the pointwise operations. For `X` an object of the site these
are the sections over `X` of the sheaf of rings attached to `R`. -/
def equivariantSubring (X : Action (Type w) G) : Subring (X.V → R) where
  carrier := {f | ∀ (g : G) (x : X.V), f (ConcreteCategory.hom (X.ρ g) x) = g • f x}
  mul_mem' hf hg g x := by
    rw [Pi.mul_apply, Pi.mul_apply, hf g x, hg g x, smul_mul']
  one_mem' g x := by rw [Pi.one_apply, Pi.one_apply, smul_one]
  add_mem' hf hg g x := by
    rw [Pi.add_apply, Pi.add_apply, hf g x, hg g x, smul_add]
  zero_mem' g x := by rw [Pi.zero_apply, Pi.zero_apply, smul_zero]
  neg_mem' hf g x := by rw [Pi.neg_apply, Pi.neg_apply, hf g x, smul_neg]

/-- A map `f : X → R` lies in `equivariantSubring G R X` if and only if it is equivariant. -/
@[simp] lemma mem_equivariantSubring {X : Action (Type w) G} {f : X.V → R} :
    f ∈ equivariantSubring G R X ↔
      ∀ (g : G) (x : X.V), f (ConcreteCategory.hom (X.ρ g) x) = g • f x :=
  Iff.rfl

/-- The sections of the sheaf of rings attached to `R` are the sections of the sheaf of sets
attached to the `G`-set `R`: this is the correspondence between rings with a `G`-action and
sheaves of rings on the site of `G`-sets. -/
def equivariantSubringEquivHom (X : Action (Type w) G) :
    (equivariantSubring G R X) ≃ (X ⟶ Action.ofMulAction G R) where
  toFun s :=
    { hom := ↾s.1
      comm := fun g => ConcreteCategory.hom_ext _ _ fun x =>
        (mem_equivariantSubring G R).1 s.2 g x }
  invFun φ :=
    ⟨ConcreteCategory.hom φ.hom, (mem_equivariantSubring G R).2 fun g x => hom_ρ_apply φ g x⟩
  left_inv _ := rfl
  right_inv _ := rfl

section Structure

variable {T : Type u} [Category.{v} T] {ι : T ⥤ Action (Type w) G} {u₀ : T}
  (α : ι.obj u₀ ≅ Action.leftRegular G) {J : GrothendieckTopology T}
  (e : Action (Type w) G ≌ Sheaf J (Type w))
  (he : e.functor ⋙ sheafToPresheaf J (Type w) =
    yoneda ⋙ (Functor.whiskeringLeft Tᵒᵖ (Action (Type w) G)ᵒᵖ (Type w)).obj ι.op)

/-- **Stacks Project, Tag 05V9.** The stalk `𝒪_p` of the sheaf of rings attached to `R` is its
ring of sections over an object presenting the regular `G`-set; with
`sectionsAtRegularRingEquiv` this is `𝒪_p = R`. -/
@[stacks 05V9 "𝒪_p = R forgetting the G-action: the stalk is the ring of sections over {}_G G"]
def stalkEquivSectionsAtRegular :
    (forgetfulPoint G e).inverseImage.obj (e.functor.obj (Action.ofMulAction G R)) ≃
      (equivariantSubring G R (ι.obj u₀)) :=
  (stalkRegularEquiv G α e he (e.functor.obj (Action.ofMulAction G R))).trans
    ((sectionsHomEquiv G e he (Action.ofMulAction G R) u₀).trans
      (equivariantSubringEquivHom G R (ι.obj u₀)).symm)

/-- **Stacks Project, Tag 05V9.** `𝒪_p = R` where we forget the `G`-action: evaluation at the
base point is a ring isomorphism from the sections of the sheaf of rings attached to `R` over an
object presenting the regular `G`-set onto `R`. -/
@[stacks 05V9 "𝒪_p = R forgetting the G-action: that ring is R"]
def sectionsAtRegularRingEquiv : (equivariantSubring G R (ι.obj u₀)) ≃+* R :=
  { (equivariantSubringEquivHom G R (ι.obj u₀)).trans
      ((α.homCongr (Iso.refl (Action.ofMulAction G R))).trans
        (leftRegularHomEquiv G (Action.ofMulAction G R))) with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

/-- `sectionsAtRegularRingEquiv` evaluates a section at the point of `ι.obj u₀` corresponding
to `1_G` under `α`. -/
@[simp] lemma sectionsAtRegularRingEquiv_apply (s : equivariantSubring G R (ι.obj u₀)) :
    sectionsAtRegularRingEquiv G R α s = s.1 (ConcreteCategory.hom α.inv.hom (1 : G)) := rfl

end Structure

end Stacks.Sites.GSets

end
