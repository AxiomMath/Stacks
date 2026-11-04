module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.Torsor
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.BaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.TorsorHomInverse

/-!
# The category of torsors for a group object over a sheaf

Let `S` be a scheme in a big fppf site, let `ℬ` be a sheaf on the big fppf site of `S` and let
`𝒢 ⟶ ℬ` be a map of sheaves carrying a group law `m : 𝒢 ×_ℬ 𝒢 ⟶ 𝒢` over `ℬ`, so that `(𝒢, m)`
is a group object of the topos `Sh((Sch/S)_fppf)/ℬ`. The category `𝒢/ℬ-Torsors` of Stacks 04UL
has as objects the triples `(U, b, F)` where `U` is an object of `(Sch/S)_fppf`, `b : U ⟶ ℬ` is
a section of `ℬ` over `U`, and `F` is a `U ×_{b, ℬ} 𝒢`-torsor over `U`; a morphism
`(U, b, F) ⟶ (U', b', F')` is a pair `(f, g)` with `f : U ⟶ U'` satisfying `b = b' ∘ f` and
`g : f^{-1}F' ⟶ F` an isomorphism of `U ×_{b, ℬ} 𝒢`-torsors. Sending `(U, b, F)` to `U` is a
functor `p : 𝒢/ℬ-Torsors ⥤ (Sch/S)_fppf`, and the fibre category over `U` is the disjoint union
over the sections `b` of `ℬ` over `U` of the categories of `U ×_{b, ℬ} 𝒢`-torsors, hence is a
groupoid.

## Main definitions

* `AlgebraicGeometry.Space.sheafPullbackGroup`: the group object `U ×_{b, ℬ} 𝒢` over `U`.
* `AlgebraicGeometry.Space.IsSheafTorsor`: the condition on a sheaf over `U` carrying an action
  of `U ×_{b, ℬ} 𝒢` that it be a `U ×_{b, ℬ} 𝒢`-torsor over `U`.
* `AlgebraicGeometry.Space.SheafTorsors`: the objects of `𝒢/ℬ-Torsors`.
* `AlgebraicGeometry.Space.SheafTorsors.Hom`, the morphisms of `𝒢/ℬ-Torsors`, and
  `AlgebraicGeometry.Space.SheafTorsors.instCategory`, the category they form.
* `AlgebraicGeometry.Space.SheafTorsors.projection`: the functor
  `p : 𝒢/ℬ-Torsors ⥤ (Sch/S)_fppf`.

## Main results

* `AlgebraicGeometry.Space.SheafTorsors.isIso_of_isIso_base`: a morphism of `𝒢/ℬ-Torsors`
  lying over an isomorphism of the site is an isomorphism. Every morphism of a fibre category
  of `p` lies over an identity, so this is the assertion that the fibre categories of `p` are
  groupoids.

## Implementation notes

A group law on `𝒢/ℬ` is a group object of the slice `Over ℬ` of presheaves on the big fppf site
of `S`, whose cartesian monoidal structure is the fibre product over `ℬ`; since a fibre product
of sheaves over a sheaf is computed sectionwise, such a group object whose underlying presheaf is
a sheaf is exactly a group object of the topos `Sh((Sch/S)_fppf)/ℬ`. The category is defined for
the presheaf data alone, the sheaf conditions on `ℬ` and on `𝒢` being needed only for the
descent properties of `p`. A section `b` of `ℬ` over `U` is a map `yoneda.obj U ⟶ ℬ`, which by
the Yoneda lemma is an element of `ℬ(U)`. The acting group is `(Over.pullback b).mapGrp.obj 𝒢`,
literally the fibre product `U ×_{b, ℬ} 𝒢` with the group law carried by the
finite-product-preserving pullback functor, so neither the group nor its law is chosen anew.

Being a `U ×_{b, ℬ} 𝒢`-torsor over `U` is the notion of Stacks 03AH for the localized site
`(Sch/U)_fppf` and the group sheaf `U ×_{b, ℬ} 𝒢` on it, rendered internally in
`Over (yoneda.obj U)`: `AlgebraicGeometry.Space.IsSheafTorsor` asks that `F` be a sheaf, that the
shear map `(g, x) ↦ (g • x, x)` be an isomorphism (`AlgebraicGeometry.IsPseudoTorsor`), and that
`F ⟶ yoneda.obj U` be locally surjective. The second condition is sectionwise simple transitivity
on each fibre, which is condition (PT) of Stacks 03AH on the localized site; the third is
condition (T), because the objects of `(Sch/U)_fppf` are the pairs `(V, u)` with `u : V ⟶ U`, the
sections of `F` over such an object are the elements of `F(V)` lying over `u`, and the covering
sieves of `(V, u)` for the localized topology are the covering sieves of `V`.

A morphism records `g : F ⟶ F'` together with cartesianness of its square over `f : U ⟶ U'`,
which says that `F` is `f^{-1}F'`; this is the source's isomorphism `f^{-1}F' ⟶ F` read through
the canonical map, and it imposes no choice of fibre product. Equivariance of `g` is the
commuting square for the two action morphisms and the canonical maps
`AlgebraicGeometry.Space.SheafTorsors.groupBaseChange` and
`AlgebraicGeometry.Space.SheafTorsors.actionBaseChange` between the relevant fibre products,
which avoids transporting a module structure along the comparison isomorphism between iterated
pullbacks.

## References

* [Stacks Project, Tag 04UL](https://stacks.math.columbia.edu/tag/04UL)
* [Stacks Project, Tag 03AH](https://stacks.math.columbia.edu/tag/03AH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory MonObj

universe u

namespace AlgebraicGeometry.Space

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}
  {B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u}

/-- The base change `U ×_{b, ℬ} 𝒢` of a group object `𝒢` over a presheaf `ℬ` along a section
`b : U ⟶ ℬ`, as a group object over `U`. -/
def sheafPullbackGroup (G : Grp (Over B)) (U : BigFppfOver 𝒞 S hS) (b : yoneda.obj U ⟶ B) :
    Grp (Over (yoneda.obj U)) :=
  (Over.pullback b).mapGrp.obj G

/-- The underlying presheaf of `U ×_{b, ℬ} 𝒢` is the fibre product of `𝒢` and `U` over `ℬ`. -/
theorem sheafPullbackGroup_X_left (G : Grp (Over B)) (U : BigFppfOver 𝒞 S hS)
    (b : yoneda.obj U ⟶ B) :
    (sheafPullbackGroup G U b).X.left = pullback G.X.hom b :=
  rfl

/-- The structure morphism of `U ×_{b, ℬ} 𝒢` is the projection to `U`. -/
theorem sheafPullbackGroup_X_hom (G : Grp (Over B)) (U : BigFppfOver 𝒞 S hS)
    (b : yoneda.obj U ⟶ B) :
    (sheafPullbackGroup G U b).X.hom = pullback.snd G.X.hom b :=
  rfl

/-- A sheaf `F` over `U` with an action of `U ×_{b, ℬ} 𝒢` is a `U ×_{b, ℬ} 𝒢`-torsor over `U`,
in the sense of Stacks 03AH for the localized site `(Sch/U)_fppf`, when the shear map of the
action is an isomorphism and `F` has sections locally on `U`. -/
abbrev IsSheafTorsor (G : Grp (Over B)) (U : BigFppfOver 𝒞 S hS) (b : yoneda.obj U ⟶ B)
    (F : Over (yoneda.obj U)) (act : ModObj (sheafPullbackGroup G U b).X F) : Prop :=
  Presheaf.IsSheaf (BigFppfOver.topology 𝒞 S hS) F.left ∧
    @AlgebraicGeometry.IsPseudoTorsor _ _ _ (sheafPullbackGroup G U b).X F _ act ∧
      Presheaf.IsLocallySurjective (BigFppfOver.topology 𝒞 S hS) F.hom

variable (G : Grp (Over B))

/-- **Stacks 04UL.** An object of the category `𝒢/ℬ-Torsors`: an object `U` of the big fppf site
of `S`, a section `b : U ⟶ ℬ` of `ℬ` over `U`, and a `U ×_{b, ℬ} 𝒢`-torsor `F` over `U`. -/
@[stacks 04UL "the objects of 𝒢/ℬ-Torsors"]
structure SheafTorsors where
  /-- The base object of the big fppf site of `S`. -/
  base : BigFppfOver 𝒞 S hS
  /-- The section `b : U ⟶ ℬ` of `ℬ` over `U`. -/
  sec : yoneda.obj base ⟶ B
  /-- The total space of the torsor, as a presheaf over `U`. -/
  total : Over (yoneda.obj base)
  /-- The action of `U ×_{b, ℬ} 𝒢` on the total space. -/
  action : ModObj (sheafPullbackGroup G base sec).X total
  /-- The total space is a `U ×_{b, ℬ} 𝒢`-torsor over `U`. -/
  isTorsor : IsSheafTorsor G base sec total action

variable {G}

namespace SheafTorsors

/-- The group object `U ×_{b, ℬ} 𝒢` acting on an object of `𝒢/ℬ-Torsors`. -/
abbrev group (T : SheafTorsors G) : Over (yoneda.obj T.base) :=
  (sheafPullbackGroup G T.base T.sec).X

/-- The action of `U ×_{b, ℬ} 𝒢` on an object of `𝒢/ℬ-Torsors`, as an instance. -/
instance instModObj (T : SheafTorsors G) : ModObj T.group T.total := T.action

/-- The total space of an object of `𝒢/ℬ-Torsors` is a sheaf. -/
theorem isSheaf (T : SheafTorsors G) :
    Presheaf.IsSheaf (BigFppfOver.topology 𝒞 S hS) T.total.left :=
  T.isTorsor.1

/-- The shear map of the action on an object of `𝒢/ℬ-Torsors` is an isomorphism. -/
theorem isPseudoTorsor (T : SheafTorsors G) :
    AlgebraicGeometry.IsPseudoTorsor T.group T.total :=
  T.isTorsor.2.1

/-- An object of `𝒢/ℬ-Torsors` has sections locally on its base. -/
theorem isLocallySurjective (T : SheafTorsors G) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology 𝒞 S hS) T.total.hom :=
  T.isTorsor.2.2

/-- The canonical morphism `U ×_{b, ℬ} 𝒢 ⟶ U' ×_{b', ℬ} 𝒢` induced by a morphism `f : U ⟶ U'`
with `b = b' ∘ f`. -/
def groupBaseChange {T T' : SheafTorsors G} (f : T.base ⟶ T'.base)
    (hf : yoneda.map f ≫ T'.sec = T.sec) :
    pullback G.X.hom T.sec ⟶ pullback G.X.hom T'.sec :=
  pullback.map _ _ _ _ (𝟙 G.X.left) (yoneda.map f) (𝟙 B) (by simp) (by simp [hf])

/-- Base change of the group does not move the `𝒢`-component. -/
@[reassoc (attr := simp)]
theorem groupBaseChange_fst {T T' : SheafTorsors G} (f : T.base ⟶ T'.base)
    (hf : yoneda.map f ≫ T'.sec = T.sec) :
    groupBaseChange f hf ≫ pullback.fst G.X.hom T'.sec = pullback.fst G.X.hom T.sec :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- Base change of the group acts by `f` on the base component. -/
@[reassoc (attr := simp)]
theorem groupBaseChange_snd {T T' : SheafTorsors G} (f : T.base ⟶ T'.base)
    (hf : yoneda.map f ≫ T'.sec = T.sec) :
    groupBaseChange f hf ≫ pullback.snd G.X.hom T'.sec =
      pullback.snd G.X.hom T.sec ≫ yoneda.map f :=
  pullback.lift_snd _ _ _

/-- The canonical morphism `(U ×_{b, ℬ} 𝒢) ×_U F ⟶ (U' ×_{b', ℬ} 𝒢) ×_{U'} F'` induced by a
morphism `f : U ⟶ U'` with `b = b' ∘ f` and a morphism `g : F ⟶ F'` over `f`. -/
def actionBaseChange {T T' : SheafTorsors G} (f : T.base ⟶ T'.base)
    (hf : yoneda.map f ≫ T'.sec = T.sec) (g : T.total.left ⟶ T'.total.left)
    (hg : T.total.hom ≫ yoneda.map f = g ≫ T'.total.hom) :
    pullback (pullback.snd G.X.hom T.sec) T.total.hom ⟶
      pullback (pullback.snd G.X.hom T'.sec) T'.total.hom :=
  pullback.map _ _ _ _ (groupBaseChange f hf) g (yoneda.map f)
    (groupBaseChange_snd f hf).symm hg

/-- Base change of the action acts by `groupBaseChange` on the group component. -/
@[reassoc (attr := simp)]
theorem actionBaseChange_fst {T T' : SheafTorsors G} (f : T.base ⟶ T'.base)
    (hf : yoneda.map f ≫ T'.sec = T.sec) (g : T.total.left ⟶ T'.total.left)
    (hg : T.total.hom ≫ yoneda.map f = g ≫ T'.total.hom) :
    actionBaseChange f hf g hg ≫ pullback.fst (pullback.snd G.X.hom T'.sec) T'.total.hom =
      pullback.fst (pullback.snd G.X.hom T.sec) T.total.hom ≫ groupBaseChange f hf :=
  pullback.lift_fst _ _ _

/-- Base change of the action acts by `g` on the torsor component. -/
@[reassoc (attr := simp)]
theorem actionBaseChange_snd {T T' : SheafTorsors G} (f : T.base ⟶ T'.base)
    (hf : yoneda.map f ≫ T'.sec = T.sec) (g : T.total.left ⟶ T'.total.left)
    (hg : T.total.hom ≫ yoneda.map f = g ≫ T'.total.hom) :
    actionBaseChange f hf g hg ≫ pullback.snd (pullback.snd G.X.hom T'.sec) T'.total.hom =
      pullback.snd (pullback.snd G.X.hom T.sec) T.total.hom ≫ g :=
  pullback.lift_snd _ _ _

/-- Base change of the group along an identity morphism is the identity. -/
@[simp]
theorem groupBaseChange_id (T : SheafTorsors G) (hf : yoneda.map (𝟙 T.base) ≫ T.sec = T.sec) :
    groupBaseChange (𝟙 T.base) hf = 𝟙 (pullback G.X.hom T.sec) := by
  apply pullback.hom_ext <;> simp

/-- Base change of the action along a pair of identity morphisms is the identity. -/
@[simp]
theorem actionBaseChange_id (T : SheafTorsors G) (hf : yoneda.map (𝟙 T.base) ≫ T.sec = T.sec)
    (hg : T.total.hom ≫ yoneda.map (𝟙 T.base) = 𝟙 T.total.left ≫ T.total.hom) :
    actionBaseChange (𝟙 T.base) hf (𝟙 T.total.left) hg = 𝟙 _ := by
  apply pullback.hom_ext <;> simp

/-- Base change of the group is compatible with composition. -/
theorem groupBaseChange_comp {T T' T'' : SheafTorsors G} (f : T.base ⟶ T'.base)
    (hf : yoneda.map f ≫ T'.sec = T.sec) (f' : T'.base ⟶ T''.base)
    (hf' : yoneda.map f' ≫ T''.sec = T'.sec) :
    groupBaseChange f hf ≫ groupBaseChange f' hf' =
      groupBaseChange (f ≫ f') (by rw [Functor.map_comp, Category.assoc, hf', hf]) := by
  apply pullback.hom_ext <;> simp

/-- Base change of the group along a pair of mutually inverse morphisms of the base composes to
the identity. -/
theorem groupBaseChange_comp_eq_id {T T' : SheafTorsors G} {f : T.base ⟶ T'.base}
    (hf : yoneda.map f ≫ T'.sec = T.sec) {f' : T'.base ⟶ T.base}
    (hf' : yoneda.map f' ≫ T.sec = T'.sec) (hff : f ≫ f' = 𝟙 T.base) :
    groupBaseChange f hf ≫ groupBaseChange f' hf' = 𝟙 (pullback G.X.hom T.sec) := by
  refine pullback.hom_ext ?_ ?_
  · simp
  · simp [← CategoryTheory.Functor.map_comp, hff]

/-- Base change of the action is compatible with composition. -/
theorem actionBaseChange_comp {T T' T'' : SheafTorsors G} (f : T.base ⟶ T'.base)
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
theorem actionBaseChange_comp_eq_id {T T' : SheafTorsors G} {f : T.base ⟶ T'.base}
    (hf : yoneda.map f ≫ T'.sec = T.sec) {g : T.total.left ⟶ T'.total.left}
    (hg : T.total.hom ≫ yoneda.map f = g ≫ T'.total.hom) {f' : T'.base ⟶ T.base}
    (hf' : yoneda.map f' ≫ T.sec = T'.sec) {g' : T'.total.left ⟶ T.total.left}
    (hg' : T'.total.hom ≫ yoneda.map f' = g' ≫ T.total.hom) (hff : f ≫ f' = 𝟙 T.base)
    (hgg : g ≫ g' = 𝟙 T.total.left) :
    actionBaseChange f hf g hg ≫ actionBaseChange f' hf' g' hg' =
      𝟙 (pullback (pullback.snd G.X.hom T.sec) T.total.hom) := by
  refine pullback.hom_ext ?_ ?_
  · simp [groupBaseChange_comp_eq_id hf hf' hff]
  · simp [hgg]

/-- **Stacks 04UL.** A morphism `(U, b, F) ⟶ (U', b', F')` of `𝒢/ℬ-Torsors`: a morphism
`f : U ⟶ U'` with `b = b' ∘ f` together with an equivariant identification of `F` with
`f^{-1}F'`. -/
@[stacks 04UL "the morphisms of 𝒢/ℬ-Torsors"]
structure Hom (T T' : SheafTorsors G) where
  /-- The morphism `f : U ⟶ U'` of the big fppf site of `S`. -/
  base : T.base ⟶ T'.base
  /-- The morphism `f` is compatible with the sections of `ℬ`, that is `b = b' ∘ f`. -/
  comp_sec : yoneda.map base ≫ T'.sec = T.sec
  /-- The morphism of total spaces. -/
  map : T.total.left ⟶ T'.total.left
  /-- The morphism of total spaces identifies `F` with `f^{-1}F'`. -/
  isPullback : IsPullback map T.total.hom T'.total.hom (yoneda.map base)
  /-- The morphism of total spaces is equivariant for the base change
  `U ×_{b, ℬ} 𝒢 ⟶ U' ×_{b', ℬ} 𝒢`. -/
  smul_comp : (γ[T.group, T.total]).left ≫ map =
    actionBaseChange base comp_sec map isPullback.w.symm ≫ (γ[T'.group, T'.total]).left

/-- A morphism of `𝒢/ℬ-Torsors` is determined by its two underlying morphisms. -/
@[ext]
theorem Hom.ext {T T' : SheafTorsors G} {φ ψ : Hom T T'} (hbase : φ.base = ψ.base)
    (hmap : φ.map = ψ.map) : φ = ψ := by
  cases φ; cases ψ; cases hbase; cases hmap; rfl

/-- The identity morphism of an object of `𝒢/ℬ-Torsors`. -/
def Hom.id (T : SheafTorsors G) : Hom T T where
  base := 𝟙 T.base
  comp_sec := by simp
  map := 𝟙 T.total.left
  isPullback := by simpa using IsPullback.id_horiz T.total.hom
  smul_comp := by
    rw [actionBaseChange_id]
    exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- The composition of two morphisms of `𝒢/ℬ-Torsors`. -/
def Hom.comp {T₁ T₂ T₃ : SheafTorsors G} (φ : Hom T₁ T₂) (ψ : Hom T₂ T₃) : Hom T₁ T₃ where
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

/-- **Stacks 04UL.** The torsors for a group object `𝒢` over a sheaf `ℬ` form a category
`𝒢/ℬ-Torsors`: morphisms compose by composing `f` and the identification of the total
spaces. -/
@[stacks 04UL "the category 𝒢/ℬ-Torsors"]
instance instCategory : Category (SheafTorsors G) where
  Hom T T' := Hom T T'
  id T := Hom.id T
  comp φ ψ := Hom.comp φ ψ
  id_comp _ := Hom.ext (Category.id_comp _) (Category.id_comp _)
  comp_id _ := Hom.ext (Category.comp_id _) (Category.comp_id _)
  assoc _ _ _ := Hom.ext (Category.assoc _ _ _) (Category.assoc _ _ _)

variable (G)

/-- **Stacks 04UL.** The functor `p : 𝒢/ℬ-Torsors ⥤ (Sch/S)_fppf` sending `(U, b, F)` to `U`,
which is how `𝒢/ℬ-Torsors` is regarded as a category over the big fppf site of `S`. -/
@[stacks 04UL "the functor p to the site"]
def projection : SheafTorsors G ⥤ BigFppfOver 𝒞 S hS where
  obj T := T.base
  map φ := Hom.base φ

variable {G}

/-- The functor `p` sends a morphism of `𝒢/ℬ-Torsors` to its morphism `f` of the site. -/
@[simp]
theorem projection_map {T T' : SheafTorsors G} (φ : T ⟶ T') :
    (projection G).map φ = Hom.base φ :=
  rfl

section Inverse

variable {T T' : SheafTorsors G} (φ : T ⟶ T') [IsIso (Hom.base φ)]

/-- The morphism of total spaces of a morphism of `𝒢/ℬ-Torsors` whose morphism `f` of the site
is an isomorphism is itself an isomorphism: the total space of the source is the fibre product
of the total space of the target with `U` over `U'`, and `f` is invertible. -/
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

/-- The morphism of `𝒢/ℬ-Torsors` inverse to a morphism whose morphism `f` of the site is an
isomorphism. -/
private def homInv : T' ⟶ T where
  base := inv (Hom.base φ)
  comp_sec := map_inv_comp_of_comp yoneda (Hom.base φ) (Hom.comp_sec φ)
  map := inv (Hom.map φ)
  isPullback := (Hom.isPullback φ).inv_fst yoneda (Hom.base φ)
  smul_comp := homInv_smul_comp φ

/-- **Stacks 04UL.** A morphism of `𝒢/ℬ-Torsors` whose morphism `f` of the big fppf site is an
isomorphism is itself an isomorphism. Every morphism of a fibre category of
`p : 𝒢/ℬ-Torsors ⥤ (Sch/S)_fppf` lies over an identity, so this says that the fibre category
over `U` — the disjoint union over the sections `b` of `ℬ` over `U` of the categories of
`U ×_{b, ℬ} 𝒢`-torsors — is a groupoid. -/
@[stacks 04UL "the fibre categories are groupoids"]
theorem isIso_of_isIso_base : IsIso φ :=
  ⟨homInv φ, Hom.ext (IsIso.hom_inv_id _) (IsIso.hom_inv_id _),
    Hom.ext (IsIso.inv_hom_id _) (IsIso.inv_hom_id _)⟩

end Inverse

end SheafTorsors

end AlgebraicGeometry.Space

end
