module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.PseudoTorsors
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.TorsorHomInverse

/-!
# Categories of torsors on the big fppf site, and the category of fppf torsors

Let `B` be an algebraic space over a scheme `S`, let `G` be a group algebraic space over `B` and
let `P` be a property of families of morphisms of presheaves on the big fppf site of `S`. The
category `TorsorsFor hB G P` has as objects the triples `(U, b, X)` where `U` is an object of
`(Sch/S)_fppf`, `b : U ⟶ B` is a morphism, and `X` is a pseudo-torsor over `U` under
`G_U = U ×_{b, B} G` trivialized by a family over `U` satisfying `P`; a morphism
`(U, b, X) ⟶ (U', b', X')` is a pair `(f, g)` with `f : U ⟶ U'` a morphism over `B` and
`g : X ⟶ U ×_{f, U'} X'` an isomorphism of `G_U`-torsors. Sending `(U, b, X)` to `U` is a functor
`p : TorsorsFor hB G P ⥤ (Sch/S)_fppf`, and the fibre category over `U` is the disjoint union
over the morphisms `b : U ⟶ B` of the categories of such torsors under `U ×_{b, B} G`, hence is a
groupoid.

Taking for `P` the fppf coverings gives the category `G-Torsors` of Stacks 04UR, which is
`AlgebraicGeometry.Space.FppfTorsors`; taking the fpqc coverings gives the category `G-Principal`
of Stacks 04UN, which is `AlgebraicGeometry.Space.PrincipalHomogeneousSpaces`. By Stacks 077B
these are different categories.

## Main definitions

* `AlgebraicGeometry.Space.fppfPullbackGroup`: the group algebraic space `G_U = U ×_{b, B} G`.
* `AlgebraicGeometry.Space.CoveringPredicate`: a property of families of morphisms to a presheaf
  on the big fppf site of `S`, and `AlgebraicGeometry.Space.CoveringPredicate.fppf`: the fppf
  coverings.
* `AlgebraicGeometry.Space.TorsorsFor`: the objects of the category of torsors trivialized by a
  family satisfying `P`, and `AlgebraicGeometry.Space.FppfTorsors`: the objects of `G-Torsors`.
* `AlgebraicGeometry.Space.TorsorsFor.Hom`, the morphisms, and
  `AlgebraicGeometry.Space.TorsorsFor.instCategory`, the category they form.
* `AlgebraicGeometry.Space.TorsorsFor.projection` and
  `AlgebraicGeometry.Space.FppfTorsors.projection`: the functor `p` to the big fppf site of `S`,
  which is how `G-Torsors` is regarded as a category over that site.

## Main results

* `AlgebraicGeometry.Space.TorsorsFor.isIso_of_isIso_base`: a morphism lying over an isomorphism
  of the site is an isomorphism. Every morphism of a fibre category of `p` lies over an identity,
  so this is the assertion that the fibre categories of `p` are groupoids.

## Implementation notes

The torsor conditions of Stacks 04TY differ only in the covering property imposed on the
trivializing family, and `AlgebraicGeometry.Space.IsTorsorFor` already carries that property as
an argument, so `TorsorsFor` carries it too: the categories of fppf torsors and of principal
homogeneous spaces are two values of one definition and share their morphisms, their base
changes and their groupoid property without the two torsor conditions being identified.

The torsor condition on an object is imposed over the base `yoneda.obj U`, which is an algebraic
space by Stacks 025Z; the acting group is the base change of `G` along `b` in the sense of
Stacks 043I, that is the image of `G` under the finite-product-preserving pullback functor on
slice categories, so neither its group structure nor the algebraicity of its underlying presheaf
is chosen anew. Base change of the group and of the action along a morphism `f : U ⟶ U'` over `B`
is expressed by the canonical maps `AlgebraicGeometry.Space.TorsorsFor.groupBaseChange` and
`AlgebraicGeometry.Space.TorsorsFor.actionBaseChange` between the relevant fibre products;
equivariance of `g` is the commuting square for those maps and the two action morphisms, which
avoids transporting a module structure along the comparison isomorphism between iterated
pullbacks. That `g` is an isomorphism onto `U ×_{f, U'} X'` is recorded as cartesianness of its
square, so no choice of fibre product is imposed.

## References

* [Stacks Project, Tag 04UR](https://stacks.math.columbia.edu/tag/04UR)
* [Stacks Project, Tag 04TY](https://stacks.math.columbia.edu/tag/04TY)
* [Stacks Project, Tag 043I](https://stacks.math.columbia.edu/tag/043I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory MonObj

universe u

namespace AlgebraicGeometry.Space

/-- A property of families of morphisms of presheaves on the big fppf site of `S` with a common
target, such as being a covering for one of the topologies of Stacks 04TY. -/
abbrev CoveringPredicate (𝒞 : BigFppfSite.{u}) (S : Scheme.{u}) (hS : 𝒞.Contains S) :=
  ∀ (T : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) (I : Type (u + 1))
    (Bᵢ : I → (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u), (∀ i, Bᵢ i ⟶ T) → Prop

/-- Being an fppf covering of the target, as a property of families of morphisms. -/
abbrev CoveringPredicate.fppf (𝒞 : BigFppfSite.{u}) (S : Scheme.{u}) (hS : 𝒞.Contains S) :
    CoveringPredicate 𝒞 S hS :=
  fun _ _ Bᵢ f => IsFppfCovering 𝒞 S hS Bᵢ f

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}
  {B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u}

/-- The base change `G_U = U ×_{b, B} G` of a group algebraic space `G` over `B` along a
morphism `b : U ⟶ B`, as a group algebraic space over `U`. -/
def fppfPullbackGroup (hB : IsAlgebraicSpace 𝒞 S hS B) (G : GroupAlgebraicSpace 𝒞 S hS B hB)
    (U : BigFppfOver 𝒞 S hS) (b : yoneda.obj U ⟶ B) :
    GroupAlgebraicSpace 𝒞 S hS (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda 𝒞 S hS U) :=
  GroupAlgebraicSpace.baseChange 𝒞 S hS
    (AlgebraicGeometry.isAlgebraicSpace_yoneda 𝒞 S hS U) b G

/-- The underlying presheaf of `G_U` is the fibre product of `G` and `U` over `B`. -/
theorem fppfPullbackGroup_X_left (hB : IsAlgebraicSpace 𝒞 S hS B)
    (G : GroupAlgebraicSpace 𝒞 S hS B hB) (U : BigFppfOver 𝒞 S hS) (b : yoneda.obj U ⟶ B) :
    (fppfPullbackGroup hB G U b).obj.X.left = pullback G.obj.X.hom b :=
  rfl

/-- The structure morphism of `G_U` is the projection to `U`. -/
theorem fppfPullbackGroup_X_hom (hB : IsAlgebraicSpace 𝒞 S hS B)
    (G : GroupAlgebraicSpace 𝒞 S hS B hB) (U : BigFppfOver 𝒞 S hS) (b : yoneda.obj U ⟶ B) :
    (fppfPullbackGroup hB G U b).obj.X.hom = pullback.snd G.obj.X.hom b :=
  rfl

variable (hB : IsAlgebraicSpace 𝒞 S hS B) (G : GroupAlgebraicSpace 𝒞 S hS B hB)

/-- An object of the category of torsors trivialized by families satisfying `P`: an object `U`
of the big fppf site of `S`, a morphism `b : U ⟶ B`, and a torsor `X` over `U` under
`G_U = U ×_{b, B} G` trivialized by a family over `U` satisfying `P`. -/
structure TorsorsFor (P : CoveringPredicate 𝒞 S hS) where
  /-- The base object of the big fppf site of `S`. -/
  base : BigFppfOver 𝒞 S hS
  /-- The morphism `b : U ⟶ B`. -/
  sec : yoneda.obj base ⟶ B
  /-- The total space of the torsor, as an object over `U`. -/
  total : Over (yoneda.obj base)
  /-- The total space is an algebraic space. -/
  isAlgebraicSpace : IsAlgebraicSpace 𝒞 S hS total.left
  /-- The action of `G_U` on the total space. -/
  action : ModObj (fppfPullbackGroup hB G base sec).obj.X total
  /-- The total space is a pseudo-torsor under `G_U` which is trivialized by a family over `U`
  satisfying `P`, in the sense of Stacks 04TY. -/
  isTorsor : @IsTorsorFor 𝒞 S hS (yoneda.obj base)
    (AlgebraicGeometry.isAlgebraicSpace_yoneda 𝒞 S hS base)
    (fppfPullbackGroup hB G base sec).obj.X total _ action
    (fppfPullbackGroup hB G base sec).property isAlgebraicSpace (P (yoneda.obj base))

/-- **Stacks 04UR.** An object of the category `G-Torsors`: an object `U` of the big fppf site
of `S`, a morphism `b : U ⟶ B`, and an fppf torsor `X` over `U` under `G_U = U ×_{b, B} G`. -/
@[stacks 04UR "the objects of G-Torsors"]
abbrev FppfTorsors := TorsorsFor hB G (CoveringPredicate.fppf 𝒞 S hS)

namespace TorsorsFor

variable {hB G} {P : CoveringPredicate 𝒞 S hS}

/-- The group algebraic space `G_U = U ×_{b, B} G` acting on a torsor. -/
abbrev group (T : TorsorsFor hB G P) : Over (yoneda.obj T.base) :=
  (fppfPullbackGroup hB G T.base T.sec).obj.X

/-- The action of `G_U` on a torsor, as an instance. -/
instance instModObj (T : TorsorsFor hB G P) : ModObj T.group T.total := T.action

/-- The shear map of the action on a torsor is an isomorphism. -/
theorem isPseudoTorsor (T : TorsorsFor hB G P) :
    AlgebraicGeometry.IsPseudoTorsor T.group T.total :=
  T.isTorsor.1

/-! ### Base change of the group and of the action -/

/-- The canonical morphism `G_U ⟶ G_{U'}` induced by a morphism `f : U ⟶ U'` over `B`. -/
def groupBaseChange {T T' : TorsorsFor hB G P} (f : T.base ⟶ T'.base)
    (hf : yoneda.map f ≫ T'.sec = T.sec) :
    pullback G.obj.X.hom T.sec ⟶ pullback G.obj.X.hom T'.sec :=
  pullback.map _ _ _ _ (𝟙 G.obj.X.left) (yoneda.map f) (𝟙 B) (by simp) (by simp [hf])

/-- Base change of the group does not move the `G`-component. -/
@[reassoc (attr := simp)]
theorem groupBaseChange_fst {T T' : TorsorsFor hB G P} (f : T.base ⟶ T'.base)
    (hf : yoneda.map f ≫ T'.sec = T.sec) :
    groupBaseChange f hf ≫ pullback.fst G.obj.X.hom T'.sec =
      pullback.fst G.obj.X.hom T.sec :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- Base change of the group acts by `f` on the base component. -/
@[reassoc (attr := simp)]
theorem groupBaseChange_snd {T T' : TorsorsFor hB G P} (f : T.base ⟶ T'.base)
    (hf : yoneda.map f ≫ T'.sec = T.sec) :
    groupBaseChange f hf ≫ pullback.snd G.obj.X.hom T'.sec =
      pullback.snd G.obj.X.hom T.sec ≫ yoneda.map f :=
  pullback.lift_snd _ _ _

/-- The canonical morphism `G_U ×_U X ⟶ G_{U'} ×_{U'} X'` induced by a morphism `f : U ⟶ U'`
over `B` and a morphism `g : X ⟶ X'` over `f`. -/
def actionBaseChange {T T' : TorsorsFor hB G P} (f : T.base ⟶ T'.base)
    (hf : yoneda.map f ≫ T'.sec = T.sec) (g : T.total.left ⟶ T'.total.left)
    (hg : T.total.hom ≫ yoneda.map f = g ≫ T'.total.hom) :
    pullback (pullback.snd G.obj.X.hom T.sec) T.total.hom ⟶
      pullback (pullback.snd G.obj.X.hom T'.sec) T'.total.hom :=
  pullback.map _ _ _ _ (groupBaseChange f hf) g (yoneda.map f)
    (groupBaseChange_snd f hf).symm hg

/-- Base change of the action acts by `groupBaseChange` on the group component. -/
@[reassoc (attr := simp)]
theorem actionBaseChange_fst {T T' : TorsorsFor hB G P} (f : T.base ⟶ T'.base)
    (hf : yoneda.map f ≫ T'.sec = T.sec) (g : T.total.left ⟶ T'.total.left)
    (hg : T.total.hom ≫ yoneda.map f = g ≫ T'.total.hom) :
    actionBaseChange f hf g hg ≫
        pullback.fst (pullback.snd G.obj.X.hom T'.sec) T'.total.hom =
      pullback.fst (pullback.snd G.obj.X.hom T.sec) T.total.hom ≫ groupBaseChange f hf :=
  pullback.lift_fst _ _ _

/-- Base change of the action acts by `g` on the total-space component. -/
@[reassoc (attr := simp)]
theorem actionBaseChange_snd {T T' : TorsorsFor hB G P} (f : T.base ⟶ T'.base)
    (hf : yoneda.map f ≫ T'.sec = T.sec) (g : T.total.left ⟶ T'.total.left)
    (hg : T.total.hom ≫ yoneda.map f = g ≫ T'.total.hom) :
    actionBaseChange f hf g hg ≫
        pullback.snd (pullback.snd G.obj.X.hom T'.sec) T'.total.hom =
      pullback.snd (pullback.snd G.obj.X.hom T.sec) T.total.hom ≫ g :=
  pullback.lift_snd _ _ _

/-- Base change of the group along an identity morphism is the identity. -/
@[simp]
theorem groupBaseChange_id (T : TorsorsFor hB G P)
    (hf : yoneda.map (𝟙 T.base) ≫ T.sec = T.sec) :
    groupBaseChange (𝟙 T.base) hf = 𝟙 (pullback G.obj.X.hom T.sec) := by
  apply pullback.hom_ext <;> simp

/-- Base change of the action along a pair of identity morphisms is the identity. -/
@[simp]
theorem actionBaseChange_id (T : TorsorsFor hB G P)
    (hf : yoneda.map (𝟙 T.base) ≫ T.sec = T.sec)
    (hg : T.total.hom ≫ yoneda.map (𝟙 T.base) = 𝟙 T.total.left ≫ T.total.hom) :
    actionBaseChange (𝟙 T.base) hf (𝟙 T.total.left) hg = 𝟙 _ := by
  apply pullback.hom_ext <;> simp

/-- Base change of the group is compatible with composition. -/
theorem groupBaseChange_comp {T T' T'' : TorsorsFor hB G P} (f : T.base ⟶ T'.base)
    (hf : yoneda.map f ≫ T'.sec = T.sec) (f' : T'.base ⟶ T''.base)
    (hf' : yoneda.map f' ≫ T''.sec = T'.sec) :
    groupBaseChange f hf ≫ groupBaseChange f' hf' =
      groupBaseChange (f ≫ f') (by rw [Functor.map_comp, Category.assoc, hf', hf]) := by
  apply pullback.hom_ext <;> simp

/-- Base change of the group along a pair of mutually inverse morphisms of the base composes to
the identity. -/
theorem groupBaseChange_comp_eq_id {T T' : TorsorsFor hB G P} {f : T.base ⟶ T'.base}
    (hf : yoneda.map f ≫ T'.sec = T.sec) {f' : T'.base ⟶ T.base}
    (hf' : yoneda.map f' ≫ T.sec = T'.sec) (hff : f ≫ f' = 𝟙 T.base) :
    groupBaseChange f hf ≫ groupBaseChange f' hf' = 𝟙 (pullback G.obj.X.hom T.sec) := by
  rw [groupBaseChange_comp]
  simp [hff]

/-- Base change of the action is compatible with composition. -/
theorem actionBaseChange_comp {T T' T'' : TorsorsFor hB G P} (f : T.base ⟶ T'.base)
    (hf : yoneda.map f ≫ T'.sec = T.sec) (g : T.total.left ⟶ T'.total.left)
    (hg : T.total.hom ≫ yoneda.map f = g ≫ T'.total.hom) (f' : T'.base ⟶ T''.base)
    (hf' : yoneda.map f' ≫ T''.sec = T'.sec) (g' : T'.total.left ⟶ T''.total.left)
    (hg' : T'.total.hom ≫ yoneda.map f' = g' ≫ T''.total.hom) :
    actionBaseChange f hf g hg ≫ actionBaseChange f' hf' g' hg' =
      actionBaseChange (f ≫ f') (by rw [Functor.map_comp, Category.assoc, hf', hf]) (g ≫ g')
        (by rw [Functor.map_comp, ← Category.assoc, hg, Category.assoc, hg',
          Category.assoc]) := by
  apply pullback.hom_ext <;> simp [groupBaseChange_comp f hf f' hf']

/-- Base change of the action along a pair of mutually inverse morphisms composes to the
identity. -/
theorem actionBaseChange_comp_eq_id {T T' : TorsorsFor hB G P} {f : T.base ⟶ T'.base}
    (hf : yoneda.map f ≫ T'.sec = T.sec) {g : T.total.left ⟶ T'.total.left}
    (hg : T.total.hom ≫ yoneda.map f = g ≫ T'.total.hom) {f' : T'.base ⟶ T.base}
    (hf' : yoneda.map f' ≫ T.sec = T'.sec) {g' : T'.total.left ⟶ T.total.left}
    (hg' : T'.total.hom ≫ yoneda.map f' = g' ≫ T.total.hom) (hff : f ≫ f' = 𝟙 T.base)
    (hgg : g ≫ g' = 𝟙 T.total.left) :
    actionBaseChange f hf g hg ≫ actionBaseChange f' hf' g' hg' =
      𝟙 (pullback (pullback.snd G.obj.X.hom T.sec) T.total.hom) := by
  rw [actionBaseChange_comp]
  simp [hff, hgg]

/-! ### The morphisms, and the category they form -/

/-- A morphism `(U, b, X) ⟶ (U', b', X')` of torsors: a morphism `f : U ⟶ U'` over `B` together
with an equivariant identification of `X` with `U ×_{f, U'} X'`. -/
@[stacks 04UR "the morphisms of G-Torsors", stacks 04UN "the morphisms of G-Principal, stated \
for an arbitrary trivializing covering property"]
structure Hom (T T' : TorsorsFor hB G P) where
  /-- The morphism `f : U ⟶ U'` of the big fppf site of `S`. -/
  base : T.base ⟶ T'.base
  /-- The morphism `f` is a morphism over `B`. -/
  comp_sec : yoneda.map base ≫ T'.sec = T.sec
  /-- The morphism of total spaces. -/
  map : T.total.left ⟶ T'.total.left
  /-- The morphism of total spaces identifies `X` with the fibre product `U ×_{f, U'} X'`. -/
  isPullback : IsPullback map T.total.hom T'.total.hom (yoneda.map base)
  /-- The morphism of total spaces is equivariant for the base change `G_U ⟶ G_{U'}`. -/
  smul_comp : (γ[T.group, T.total]).left ≫ map =
    actionBaseChange base comp_sec map isPullback.w.symm ≫ (γ[T'.group, T'.total]).left

/-- A morphism of torsors is determined by its two underlying morphisms. -/
@[ext]
theorem Hom.ext {T T' : TorsorsFor hB G P} {φ ψ : Hom T T'} (hbase : φ.base = ψ.base)
    (hmap : φ.map = ψ.map) : φ = ψ := by
  cases φ; cases ψ; cases hbase; cases hmap; rfl

/-- The identity morphism of a torsor. -/
def Hom.id (T : TorsorsFor hB G P) : Hom T T where
  base := 𝟙 T.base
  comp_sec := by simp
  map := 𝟙 T.total.left
  isPullback := by simpa using IsPullback.id_horiz T.total.hom
  smul_comp := by
    rw [actionBaseChange_id]
    exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- The composition of two morphisms of torsors. -/
def Hom.comp {T₁ T₂ T₃ : TorsorsFor hB G P} (φ : Hom T₁ T₂) (ψ : Hom T₂ T₃) : Hom T₁ T₃ where
  base := φ.base ≫ ψ.base
  comp_sec := by rw [Functor.map_comp, Category.assoc, ψ.comp_sec, φ.comp_sec]
  map := φ.map ≫ ψ.map
  isPullback := by simpa using φ.isPullback.paste_horiz ψ.isPullback
  smul_comp := by
    refine Eq.trans ?_ (congrArg (· ≫ (γ[T₃.group, T₃.total]).left)
      (actionBaseChange_comp φ.base φ.comp_sec φ.map φ.isPullback.w.symm ψ.base ψ.comp_sec
        ψ.map ψ.isPullback.w.symm))
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ ψ.map) φ.smul_comp).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (actionBaseChange φ.base φ.comp_sec φ.map φ.isPullback.w.symm ≫ ·)
      ψ.smul_comp).trans ?_
    exact (Category.assoc _ _ _).symm

/-- The torsors under a group algebraic space `G` over `B` which are trivialized by a family
satisfying `P` form a category: morphisms compose by composing `f` and the identification of the
total spaces. -/
@[stacks 04UR "the category G-Torsors", stacks 04UN "the category G-Principal, whose \
composition is stated for an arbitrary trivializing covering property"]
instance instCategory : Category (TorsorsFor hB G P) where
  Hom T T' := Hom T T'
  id T := Hom.id T
  comp φ ψ := Hom.comp φ ψ
  id_comp _ := Hom.ext (Category.id_comp _) (Category.id_comp _)
  comp_id _ := Hom.ext (Category.comp_id _) (Category.comp_id _)
  assoc _ _ _ := Hom.ext (Category.assoc _ _ _) (Category.assoc _ _ _)

variable (hB G P)

/-- The functor `p` sending `(U, b, X)` to `U`, which is how a category of torsors is regarded
as a category over the big fppf site of `S`. -/
def projection : TorsorsFor hB G P ⥤ BigFppfOver 𝒞 S hS where
  obj T := T.base
  map φ := Hom.base φ

variable {hB G P}

/-- The functor `p` sends a morphism of torsors to its morphism `f` of the site. -/
@[simp]
theorem projection_map {T T' : TorsorsFor hB G P} (φ : T ⟶ T') :
    (projection hB G P).map φ = Hom.base φ :=
  rfl

/-! ### The fibre categories are groupoids -/

section Inverse

variable {T T' : TorsorsFor hB G P} (φ : T ⟶ T') [IsIso (Hom.base φ)]

/-- The morphism of total spaces of a morphism of torsors whose morphism `f` of the site is an
isomorphism is itself an isomorphism: the total space of the source is the fibre product of the
total space of the target with `U` over `U'`, and `f` is invertible. -/
private instance : IsIso (Hom.map φ) := (Hom.isPullback φ).isIso_fst_of_isIso

private theorem homInv_actionBaseChange_comp :
    actionBaseChange (inv (Hom.base φ))
        (map_inv_comp_of_comp yoneda (Hom.base φ) (Hom.comp_sec φ)) (inv (Hom.map φ))
        ((Hom.isPullback φ).hom_comp_map_inv yoneda (Hom.base φ)) ≫
      actionBaseChange (Hom.base φ) (Hom.comp_sec φ) (Hom.map φ)
        (Hom.isPullback φ).w.symm = 𝟙 _ :=
  actionBaseChange_comp_eq_id (map_inv_comp_of_comp yoneda (Hom.base φ) (Hom.comp_sec φ))
    ((Hom.isPullback φ).hom_comp_map_inv yoneda (Hom.base φ)) (Hom.comp_sec φ)
    (Hom.isPullback φ).w.symm (IsIso.inv_hom_id (Hom.base φ)) (IsIso.inv_hom_id (Hom.map φ))

private theorem homInv_smul_comp :
    (γ[T'.group, T'.total]).left ≫ inv (Hom.map φ) =
      actionBaseChange (inv (Hom.base φ))
          (map_inv_comp_of_comp yoneda (Hom.base φ) (Hom.comp_sec φ)) (inv (Hom.map φ))
          ((Hom.isPullback φ).hom_comp_map_inv yoneda (Hom.base φ)) ≫
        (γ[T.group, T.total]).left :=
  comp_eq_of_comp_eq (homInv_actionBaseChange_comp φ) (IsIso.hom_inv_id (Hom.map φ))
    (Hom.smul_comp φ)

/-- The morphism of torsors inverse to a morphism whose morphism `f` of the site is an
isomorphism. -/
private def homInv : T' ⟶ T where
  base := inv (Hom.base φ)
  comp_sec := map_inv_comp_of_comp yoneda (Hom.base φ) (Hom.comp_sec φ)
  map := inv (Hom.map φ)
  isPullback := (Hom.isPullback φ).inv_fst yoneda (Hom.base φ)
  smul_comp := homInv_smul_comp φ

/-- A morphism of torsors whose morphism `f` of the big fppf site is an isomorphism is itself an
isomorphism. Every morphism of a fibre category of the functor `p` to the site lies over an
identity, so this says that the fibre category over `U` — the disjoint union over the morphisms
`b : U ⟶ B` of the categories of torsors under `U ×_{b, B} G` trivialized by a family satisfying
`P` — is a groupoid. -/
@[stacks 04UR "the fibre categories are groupoids", stacks 04UN "the fibre categories of \
p : G-Principal ⥤ (Sch/S)_fppf are groupoids, by the assertion for an arbitrary trivializing \
covering property"]
theorem isIso_of_isIso_base : IsIso φ :=
  ⟨homInv φ, Hom.ext (IsIso.hom_inv_id _) (IsIso.hom_inv_id _),
    Hom.ext (IsIso.inv_hom_id _) (IsIso.inv_hom_id _)⟩

end Inverse

end TorsorsFor

namespace FppfTorsors

/-- **Stacks 04UR.** The functor `p : G-Torsors ⥤ (Sch/S)_fppf` sending `(U, b, X)` to `U`,
which is how `G-Torsors` is regarded as a category over the big fppf site of `S`. -/
@[stacks 04UR "the functor p to the site"]
abbrev projection : FppfTorsors hB G ⥤ BigFppfOver 𝒞 S hS :=
  TorsorsFor.projection hB G (CoveringPredicate.fppf 𝒞 S hS)

end FppfTorsors

end AlgebraicGeometry.Space

end
