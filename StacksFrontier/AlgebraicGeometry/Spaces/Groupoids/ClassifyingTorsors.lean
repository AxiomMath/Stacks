module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.Torsor
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupActions
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The category of torsors under a group object over a sheaf

Let `S` be a scheme in a big fppf site, let `ℬ` be a presheaf on the big fppf site of `S` and
let `𝒢` be a group object of the slice over `ℬ`, that is, a map `𝒢 ⟶ ℬ` together with a group
law `m : 𝒢 ×_ℬ 𝒢 ⟶ 𝒢` over `ℬ`. The category `𝒢/ℬ-Torsors` has as objects the triples
`(U, b, F)` with `U` an object of the site, `b : U ⟶ ℬ` a section of `ℬ` over `U` and `F` a
`U ×_{b, ℬ} 𝒢`-torsor over `U`; a morphism `(U, b, F) ⟶ (U', b', F')` is a morphism
`f : U ⟶ U'` with `b = b' ∘ f` together with an equivariant identification of `F` with
`f^{-1}F'`.

## Main definitions

* `AlgebraicGeometry.ClassifyingTorsors.pullbackGroup` is the group object `U ×_{b, ℬ} 𝒢`
  over `U`.
* `AlgebraicGeometry.ClassifyingTorsors.IsTorsor` is the condition that a sheaf over `U` with
  an action of `U ×_{b, ℬ} 𝒢` is a `U ×_{b, ℬ} 𝒢`-torsor over `U`.
* `AlgebraicGeometry.ClassifyingTorsors.Torsor` and
  `AlgebraicGeometry.ClassifyingTorsors.TorsorHom` are the objects and morphisms of
  `𝒢/ℬ-Torsors`.
* `AlgebraicGeometry.ClassifyingTorsors.torsorsProjection` is the projection
  `p : 𝒢/ℬ-Torsors ⥤ (Sch/S)_fppf`.

## Implementation notes

A group law on `𝒢/ℬ` is a group object of the slice `Over ℬ` of presheaves, whose cartesian
monoidal structure is the fibre product over `ℬ`; since a fibre product of sheaves over a
sheaf is computed sectionwise, such a group object with sheaf underlying presheaf is a group
object of the topos of sheaves sliced over `ℬ`. The sheaf conditions on `ℬ` and `𝒢` are
therefore not built into the category, which is defined for the presheaf data alone. A
section `b` of `ℬ` over `U` is a map `yoneda.obj U ⟶ ℬ`, which by the Yoneda lemma is an
element of `ℬ(U)`. The acting group is `(Over.pullback b).mapGrp.obj 𝒢`, literally the fibre
product `U ×_{b, ℬ} 𝒢` with its group law carried by the finite-product-preserving pullback
functor.

Being a `U ×_{b, ℬ} 𝒢`-torsor over `U` is rendered internally in `Over (yoneda.obj U)`: `F`
is a sheaf, the shear map `(g, x) ↦ (g • x, x)` is an isomorphism, and `F ⟶ yoneda.obj U` is
locally surjective. A morphism records `g : F ⟶ F'` together with cartesianness of its square
over `f`, which says that `F` is `f^{-1}F'`, and equivariance of `g` as the commuting square
for the two action morphisms and the canonical maps between the relevant fibre products.

## References

* [Stacks Project, Tag 04UJ](https://stacks.math.columbia.edu/tag/04UJ)
* [Stacks Project, Tag 04UL](https://stacks.math.columbia.edu/tag/04UL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory MonObj

universe u w

namespace AlgebraicGeometry.ClassifyingTorsors

variable {𝒞 : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}
  {B : (AlgebraicGeometry.BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u}

/-- The base change `U ×_{b, ℬ} 𝒢` of a group object `𝒢` over `ℬ` along a section
`b : U ⟶ ℬ`, as a group object over `U`. -/
public def pullbackGroup (G : Grp (Over B)) (U : AlgebraicGeometry.BigFppfOver 𝒞 S hS)
    (b : yoneda.obj U ⟶ B) : Grp (Over (yoneda.obj U)) :=
  (Over.pullback b).mapGrp.obj G

/-- The underlying presheaf of `U ×_{b, ℬ} 𝒢` is the fibre product of `𝒢` and `U` over
`ℬ`. -/
public theorem pullbackGroup_X_left (G : Grp (Over B))
    (U : AlgebraicGeometry.BigFppfOver 𝒞 S hS) (b : yoneda.obj U ⟶ B) :
    (pullbackGroup G U b).X.left = pullback G.X.hom b := rfl

/-- The structure morphism of `U ×_{b, ℬ} 𝒢` is the projection to `U`. -/
public theorem pullbackGroup_X_hom (G : Grp (Over B))
    (U : AlgebraicGeometry.BigFppfOver 𝒞 S hS) (b : yoneda.obj U ⟶ B) :
    (pullbackGroup G U b).X.hom = pullback.snd G.X.hom b := rfl

/-- A sheaf `F` over `U` with an action of `U ×_{b, ℬ} 𝒢` is a `U ×_{b, ℬ} 𝒢`-torsor over
`U`, in the sense of Stacks 03AH for the localized site `(Sch/U)_fppf`, when the shear map
of the action is an isomorphism and `F` has sections locally on `U`. -/
public abbrev IsTorsor (G : Grp (Over B)) (U : AlgebraicGeometry.BigFppfOver 𝒞 S hS)
    (b : yoneda.obj U ⟶ B) (F : Over (yoneda.obj U))
    (act : ModObj (pullbackGroup G U b).X F) : Prop :=
  Presheaf.IsSheaf (AlgebraicGeometry.BigFppfOver.topology 𝒞 S hS) F.left ∧
    @AlgebraicGeometry.IsPseudoTorsor _ _ _ (pullbackGroup G U b).X F _ act ∧
      Presheaf.IsLocallySurjective (AlgebraicGeometry.BigFppfOver.topology 𝒞 S hS) F.hom

variable (G : Grp (Over B))

/-- An object of `𝒢/ℬ-Torsors`: a scheme `U` in the big fppf site of `S`, a section
`b : U ⟶ ℬ` of `ℬ` over `U`, and a `U ×_{b, ℬ} 𝒢`-torsor `F` over `U`. -/
@[sga "4 XVIII 1.3.9" "more general"]
public structure Torsor where
  /-- The base scheme, an object of the big fppf site of `S`. -/
  U : AlgebraicGeometry.BigFppfOver 𝒞 S hS
  /-- The section `b : U ⟶ ℬ` of `ℬ` over `U`. -/
  b : yoneda.obj U ⟶ B
  /-- The total space, as a presheaf over `U`. -/
  F : Over (yoneda.obj U)
  /-- The action of `U ×_{b, ℬ} 𝒢` on `F`. -/
  action : ModObj (pullbackGroup G U b).X F
  /-- `F` is a `U ×_{b, ℬ} 𝒢`-torsor over `U`. -/
  isTorsor : IsTorsor G U b F action

variable {G}

namespace Torsor

/-- The group object `U ×_{b, ℬ} 𝒢` acting on a torsor. -/
public abbrev group (T : Torsor G) : Over (yoneda.obj T.U) :=
  (pullbackGroup G T.U T.b).X

/-- The action of `U ×_{b, ℬ} 𝒢` on a torsor, as an instance. -/
public instance instModObj (T : Torsor G) : ModObj T.group T.F := T.action

/-- The underlying presheaf of a torsor is a sheaf. -/
public theorem isSheaf (T : Torsor G) :
    Presheaf.IsSheaf (AlgebraicGeometry.BigFppfOver.topology 𝒞 S hS) T.F.left :=
  T.isTorsor.1

/-- The shear map of the action on a torsor is an isomorphism. -/
public theorem isPseudoTorsor (T : Torsor G) :
    AlgebraicGeometry.IsPseudoTorsor T.group T.F :=
  T.isTorsor.2.1

/-- A torsor has sections locally on its base. -/
public theorem isLocallySurjective (T : Torsor G) :
    Presheaf.IsLocallySurjective (AlgebraicGeometry.BigFppfOver.topology 𝒞 S hS) T.F.hom :=
  T.isTorsor.2.2

end Torsor

/-- The canonical morphism `U ×_{b, ℬ} 𝒢 ⟶ U' ×_{b', ℬ} 𝒢` induced by a morphism
`f : U ⟶ U'` with `b = b' ∘ f`. -/
@[reducible] public def groupBaseChange {T T' : Torsor G} (f : T.U ⟶ T'.U)
    (hf : yoneda.map f ≫ T'.b = T.b) :
    pullback G.X.hom T.b ⟶ pullback G.X.hom T'.b :=
  pullback.map _ _ _ _ (𝟙 G.X.left) (yoneda.map f) (𝟙 B) (by simp) (by simp [hf])

/-- Base change of the group does not move the `𝒢`-component. -/
@[reassoc (attr := simp)]
public theorem groupBaseChange_fst {T T' : Torsor G} (f : T.U ⟶ T'.U)
    (hf : yoneda.map f ≫ T'.b = T.b) :
    groupBaseChange f hf ≫ pullback.fst G.X.hom T'.b = pullback.fst G.X.hom T.b :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- Base change of the group acts by `f` on the base component. -/
@[reassoc (attr := simp)]
public theorem groupBaseChange_snd {T T' : Torsor G} (f : T.U ⟶ T'.U)
    (hf : yoneda.map f ≫ T'.b = T.b) :
    groupBaseChange f hf ≫ pullback.snd G.X.hom T'.b =
      pullback.snd G.X.hom T.b ≫ yoneda.map f :=
  pullback.lift_snd _ _ _

/-- The canonical morphism `(U ×_{b, ℬ} 𝒢) ×_U F ⟶ (U' ×_{b', ℬ} 𝒢) ×_{U'} F'` induced by
a morphism `f : U ⟶ U'` with `b = b' ∘ f` and a morphism `g : F ⟶ F'` over `f`. -/
@[reducible] public def actionBaseChange {T T' : Torsor G} (f : T.U ⟶ T'.U)
    (hf : yoneda.map f ≫ T'.b = T.b) (g : T.F.left ⟶ T'.F.left)
    (hg : T.F.hom ≫ yoneda.map f = g ≫ T'.F.hom) :
    pullback (pullback.snd G.X.hom T.b) T.F.hom ⟶
      pullback (pullback.snd G.X.hom T'.b) T'.F.hom :=
  pullback.map _ _ _ _ (groupBaseChange f hf) g (yoneda.map f)
    (groupBaseChange_snd f hf).symm hg

/-- Base change of the action acts by `groupBaseChange` on the group component. -/
@[reassoc (attr := simp)]
public theorem actionBaseChange_fst {T T' : Torsor G} (f : T.U ⟶ T'.U)
    (hf : yoneda.map f ≫ T'.b = T.b) (g : T.F.left ⟶ T'.F.left)
    (hg : T.F.hom ≫ yoneda.map f = g ≫ T'.F.hom) :
    actionBaseChange f hf g hg ≫
        pullback.fst (pullback.snd G.X.hom T'.b) T'.F.hom =
      pullback.fst (pullback.snd G.X.hom T.b) T.F.hom ≫ groupBaseChange f hf :=
  pullback.lift_fst _ _ _

/-- Base change of the action acts by `g` on the torsor component. -/
@[reassoc (attr := simp)]
public theorem actionBaseChange_snd {T T' : Torsor G} (f : T.U ⟶ T'.U)
    (hf : yoneda.map f ≫ T'.b = T.b) (g : T.F.left ⟶ T'.F.left)
    (hg : T.F.hom ≫ yoneda.map f = g ≫ T'.F.hom) :
    actionBaseChange f hf g hg ≫
        pullback.snd (pullback.snd G.X.hom T'.b) T'.F.hom =
      pullback.snd (pullback.snd G.X.hom T.b) T.F.hom ≫ g :=
  pullback.lift_snd _ _ _

/-- Base change of the group along an identity morphism is the identity. -/
@[simp]
public theorem groupBaseChange_id (T : Torsor G)
    (hf : yoneda.map (𝟙 T.U) ≫ T.b = T.b) :
    groupBaseChange (𝟙 T.U) hf = 𝟙 (pullback G.X.hom T.b) := by
  apply pullback.hom_ext <;> simp

/-- Base change of the action along a pair of identity morphisms is the identity. -/
@[simp]
public theorem actionBaseChange_id (T : Torsor G)
    (hf : yoneda.map (𝟙 T.U) ≫ T.b = T.b)
    (hg : T.F.hom ≫ yoneda.map (𝟙 T.U) = 𝟙 T.F.left ≫ T.F.hom) :
    actionBaseChange (𝟙 T.U) hf (𝟙 T.F.left) hg = 𝟙 _ := by
  apply pullback.hom_ext <;> simp

/-- Base change of the group is compatible with composition. -/
public theorem groupBaseChange_comp {T T' T'' : Torsor G} (f : T.U ⟶ T'.U)
    (hf : yoneda.map f ≫ T'.b = T.b) (f' : T'.U ⟶ T''.U)
    (hf' : yoneda.map f' ≫ T''.b = T'.b) :
    groupBaseChange f hf ≫ groupBaseChange f' hf' =
      groupBaseChange (f ≫ f') (by rw [Functor.map_comp, Category.assoc, hf', hf]) := by
  apply pullback.hom_ext <;> simp

/-- Base change of the action is compatible with composition. -/
public theorem actionBaseChange_comp {T T' T'' : Torsor G} (f : T.U ⟶ T'.U)
    (hf : yoneda.map f ≫ T'.b = T.b) (g : T.F.left ⟶ T'.F.left)
    (hg : T.F.hom ≫ yoneda.map f = g ≫ T'.F.hom) (f' : T'.U ⟶ T''.U)
    (hf' : yoneda.map f' ≫ T''.b = T'.b) (g' : T'.F.left ⟶ T''.F.left)
    (hg' : T'.F.hom ≫ yoneda.map f' = g' ≫ T''.F.hom) :
    actionBaseChange f hf g hg ≫ actionBaseChange f' hf' g' hg' =
      actionBaseChange (f ≫ f') (by rw [Functor.map_comp, Category.assoc, hf', hf])
        (g ≫ g')
        (by rw [Functor.map_comp, ← Category.assoc, hg, Category.assoc, hg',
          Category.assoc]) := by
  apply pullback.hom_ext <;> simp [groupBaseChange_comp f hf f' hf']

/-- A morphism `(U, b, F) ⟶ (U', b', F')` of `𝒢/ℬ`-torsors: a morphism `f : U ⟶ U'` with
`b = b' ∘ f` together with an equivariant identification of `F` with `f^{-1}F'`. -/
@[sga "4 XVIII 1.3.9" "more general"]
public structure TorsorHom (T T' : Torsor G) where
  /-- The morphism of base schemes. -/
  f : T.U ⟶ T'.U
  /-- The morphism `f` is compatible with the sections of `ℬ`. -/
  comp_b : yoneda.map f ≫ T'.b = T.b
  /-- The morphism of total spaces. -/
  g : T.F.left ⟶ T'.F.left
  /-- The morphism `g` identifies `F` with `f^{-1}F'`. -/
  isPullback : IsPullback g T.F.hom T'.F.hom (yoneda.map f)
  /-- The morphism `g` is equivariant for the base change
  `U ×_{b, ℬ} 𝒢 ⟶ U' ×_{b', ℬ} 𝒢`. -/
  smul_comp : (γ[T.group, T.F]).left ≫ g =
    actionBaseChange f comp_b g isPullback.w.symm ≫ (γ[T'.group, T'.F]).left

/-- A morphism of `𝒢/ℬ`-torsors is determined by its two underlying morphisms. -/
@[ext] public theorem TorsorHom.ext {T T' : Torsor G} {φ ψ : TorsorHom T T'}
    (hf : φ.f = ψ.f) (hg : φ.g = ψ.g) : φ = ψ := by
  cases φ; cases ψ; cases hf; cases hg; rfl

/-- Identities and composition of `𝒢/ℬ`-torsors, taken componentwise. -/
public instance torsorCategoryStruct : CategoryStruct (Torsor G) where
  Hom := TorsorHom
  id T :=
    { f := 𝟙 T.U
      comp_b := by simp
      g := 𝟙 T.F.left
      isPullback := by simpa using IsPullback.id_horiz T.F.hom
      smul_comp := by
        rw [actionBaseChange_id]
        exact (Category.comp_id _).trans (Category.id_comp _).symm }
  comp {T₁ T₂ T₃} φ ψ :=
    { f := φ.f ≫ ψ.f
      comp_b := by rw [Functor.map_comp, Category.assoc, ψ.comp_b, φ.comp_b]
      g := φ.g ≫ ψ.g
      isPullback := by simpa using φ.isPullback.paste_horiz ψ.isPullback
      smul_comp := by
        refine Eq.trans ?_ (congrArg (· ≫ (γ[T₃.group, T₃.F]).left)
          (actionBaseChange_comp φ.f φ.comp_b φ.g φ.isPullback.w.symm ψ.f ψ.comp_b
            ψ.g ψ.isPullback.w.symm))
        refine (Category.assoc _ _ _).symm.trans ?_
        refine (congrArg (· ≫ ψ.g) φ.smul_comp).trans ?_
        refine (Category.assoc _ _ _).trans ?_
        refine (congrArg (actionBaseChange φ.f φ.comp_b φ.g φ.isPullback.w.symm ≫ ·)
          ψ.smul_comp).trans ?_
        exact (Category.assoc _ _ _).symm }

/-- `𝒢/ℬ-Torsors` is a category. -/
public instance torsorCategory : Category (Torsor G) where
  toCategoryStruct := torsorCategoryStruct
  id_comp φ := TorsorHom.ext (Category.id_comp φ.f) (Category.id_comp φ.g)
  comp_id φ := TorsorHom.ext (Category.comp_id φ.f) (Category.comp_id φ.g)
  assoc φ ψ χ := TorsorHom.ext (Category.assoc φ.f ψ.f χ.f) (Category.assoc φ.g ψ.g χ.g)

variable (G)

/-- The projection `p : 𝒢/ℬ-Torsors ⥤ (Sch/S)_fppf`, sending `(U, b, F)` to `U`. -/
@[sga "4 XVIII 1.3.9" "partial"]
public def torsorsProjection : Torsor G ⥤ AlgebraicGeometry.BigFppfOver 𝒞 S hS where
  obj T := T.U
  map φ := φ.f
  map_id _ := rfl
  map_comp _ _ := rfl
end AlgebraicGeometry.ClassifyingTorsors

end
