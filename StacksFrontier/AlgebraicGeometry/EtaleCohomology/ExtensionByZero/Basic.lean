module

public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Extension by zero on the small étale site

Let `j : U ⟶ X` be an étale morphism of schemes.  Composition with `j` carries a scheme étale
over `U` to a scheme étale over `X`, hence defines a functor `U_étale ⥤ X_étale` between the
small étale sites.  This file shows that this functor is a continuous and cocontinuous functor of
sites, and deduces the three functors it induces on abelian sheaves:

* restriction `j^{-1}`, which is literally precomposition: `(j^{-1} G)(V) = G(V)` for `V` étale
  over `U`;
* its right adjoint, the direct image `j_*`;
* its left adjoint, the **extension by zero** `j_!`.

This is Stacks Tag 03S3, parts (1) (sheaves of sets) and (2) (abelian sheaves); the variant for
sheaves of modules over a sheaf of rings, part (3), is not treated here.

## Main definitions

* `AlgebraicGeometry.Scheme.Etale.smallEtaleCompose`: composition with an étale morphism, as a
  functor between small étale sites.
* `Stacks.EtaleCohomology.etaleRestrictionSets` and
  `Stacks.EtaleCohomology.extensionByZeroSets`: restriction and extension by zero on sheaves of
  sets.
* `Stacks.EtaleCohomology.etaleRestriction`: the restriction functor `j^{-1}` on abelian
  sheaves.
* `Stacks.EtaleCohomology.etaleDirectImage`: the direct image `j_*` on abelian sheaves.
* `Stacks.EtaleCohomology.extensionByZero`: extension by zero `j_!` on abelian sheaves.

## Main results

* `AlgebraicGeometry.Scheme.Etale.smallEtaleCompose_coverPreserving`,
  `AlgebraicGeometry.Scheme.Etale.smallEtaleCompose_compatiblePreserving`,
  `AlgebraicGeometry.Scheme.Etale.smallEtaleCompose_isContinuous` and
  `AlgebraicGeometry.Scheme.Etale.smallEtaleCompose_isCocontinuous`: composition with an étale
  morphism is a continuous and cocontinuous cover-preserving functor of sites.
* `AlgebraicGeometry.Scheme.Etale.smallEtaleComposeBaseChangeAdj`: composition with `j` is left
  adjoint to base change along `j`.
* `Stacks.EtaleCohomology.extensionByZeroSetsAdj` and
  `Stacks.EtaleCohomology.extensionByZeroAdj`: `j_! ⊣ j^{-1}`, on sheaves of sets and on abelian
  sheaves.
* `Stacks.EtaleCohomology.etaleDirectImageAdj`: `j^{-1} ⊣ j_*`.
* `Stacks.EtaleCohomology.extensionByZeroHomEquiv`: the characterising functorial bijection
  `Hom_X(j_! F, G) ≃ Hom_U(F, j^{-1} G)`.

## Implementation notes

The small étale site of a scheme `X` is Mathlib's `AlgebraicGeometry.Scheme.Etale`, that is
`CategoryTheory.MorphismProperty.Over @Etale ⊤ X`, with the topology
`AlgebraicGeometry.Scheme.smallEtaleTopology`.  Composition with `j` is
`CategoryTheory.MorphismProperty.Over.map`, which leaves the underlying scheme of an object and
the underlying morphism of a morphism untouched and only changes the structure morphism to `X`.
Since the small étale topology is detected pointwise on underlying spaces
(`Stacks.EtaleCohomology.mem_smallEtaleTopology_iff`), cover preservation and cocontinuity are
immediate from that description; compatible preservation is the argument of Mathlib's
`CategoryTheory.GrothendieckTopology.over_map_compatiblePreserving` for slice categories,
carried out in the étale subcategory, where the auxiliary object needs the extra input that
étale morphisms compose.

Note that composition with `j` is *not* full unless `j` is a monomorphism, so Mathlib's
`CategoryTheory.compatiblePreservingOfDownwardsClosed` does not apply, and it is not
representably flat (the comma categories are empty over objects admitting no map to `U`), so
`CategoryTheory.compatiblePreservingOfFlat` does not apply either.

`j_!` is realised through `CategoryTheory.Functor.sheafPullbackConstruction.sheafPullback`, that
is as the sheafification of the left Kan extension along composition with `j`.  The explicit
description of that left Kan extension as the presheaf `V ↦ ⨁_{V → U} F(V → U)` of Stacks Tag
0F4K is *not* proved here; everything in this file uses only the universal property.

The repository already has an inverse image on abelian sheaves of small étale sites for an
arbitrary morphism of schemes, `Stacks.EtaleCohomology.etaleAbelianInverseImage`, built as the
sheafified left Kan extension along *base change*.  For an étale `j` that functor and
`Stacks.EtaleCohomology.etaleRestriction` are both reasonable readings of `j^{-1}`; identifying
them is a Beck–Chevalley statement that is not proved here.

## References

* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
* [Stacks Project, Tag 03S4](https://stacks.math.columbia.edu/tag/03S4)
* [Stacks Project, Tag 0F4K](https://stacks.math.columbia.edu/tag/0F4K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace AlgebraicGeometry.Etale

/-- Being étale is stable under composition, as a statement about the morphism property
`@AlgebraicGeometry.Etale` rather than about individual morphisms.  Mathlib has this bundled
only inside `AlgebraicGeometry.Etale.instIsMultiplicativeScheme`, from which typeclass
inference does not extract it. -/
@[sga "1 I 4.6"]
theorem isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition (@Etale : MorphismProperty Scheme.{u}) :=
  Etale.instIsMultiplicativeScheme.toIsStableUnderComposition

end AlgebraicGeometry.Etale

attribute [local instance] AlgebraicGeometry.Etale.isStableUnderComposition
attribute [local instance] AlgebraicGeometry.Etale.instIsMultiplicativeScheme

namespace AlgebraicGeometry.Scheme.Etale

variable {U X : Scheme.{u}} (j : U ⟶ X)

/-- Composition with an étale morphism `j : U ⟶ X`, as a functor from the small étale site of
`U` to the small étale site of `X`: a scheme étale over `U` is étale over `X`. -/
def smallEtaleCompose [hj : Etale j] : U.Etale ⥤ X.Etale :=
  MorphismProperty.Over.map (P := @Etale) ⊤ hj

variable [hj : Etale j]

/-- Composition with `j` does not change the underlying scheme of an object. -/
@[simp]
theorem smallEtaleCompose_obj_left (V : U.Etale) : ((smallEtaleCompose j).obj V).left = V.left :=
  rfl

/-- Composition with `j` sends an object with structure morphism `V.hom` to the object with
structure morphism `V.hom ≫ j`. -/
@[simp]
theorem smallEtaleCompose_obj_hom (V : U.Etale) :
    ((smallEtaleCompose j).obj V).hom = V.hom ≫ j :=
  rfl

/-- Composition with `j` does not change the underlying morphism of a morphism. -/
@[simp]
theorem smallEtaleCompose_map_left {V W : U.Etale} (f : V ⟶ W) :
    ((smallEtaleCompose j).map f).left = f.left :=
  rfl

/-- A morphism `f : W ⟶ j_* V` of the small étale site of `X` into the image of an object `V` of
the small étale site of `U` makes the source of `f` into a scheme étale over `U`, via
`f.left ≫ V.hom`: both factors are étale, `f.left` because it is a morphism of the small étale
site of `X` and `V.hom` because `V` is an object of the small étale site of `U`. -/
theorem etale_left_comp_hom {V : U.Etale} {W : X.Etale}
    (f : W ⟶ (smallEtaleCompose j).obj V) : Etale (f.left ≫ V.hom) :=
  MorphismProperty.comp_mem _ _ _ inferInstance V.prop

/-- The object of the small étale site of `U` obtained from a morphism of the small étale site
of `X` into the image of an object `V` of the small étale site of `U`: its underlying scheme is
the source of the morphism, and its structure morphism to `U` is the composite with `V.hom`. -/
def composeDescend {V : U.Etale} {W : X.Etale} (f : W ⟶ (smallEtaleCompose j).obj V) :
    U.Etale :=
  MorphismProperty.Over.mk ⊤ (f.left ≫ V.hom) (etale_left_comp_hom j f)

/-- The underlying scheme of `composeDescend j f` is the source of `f`. -/
@[simp]
theorem composeDescend_left {V : U.Etale} {W : X.Etale} (f : W ⟶ (smallEtaleCompose j).obj V) :
    (composeDescend j f).left = W.left :=
  rfl

/-- The structure morphism of `composeDescend j f` to `U` is `f.left ≫ V.hom`. -/
@[simp]
theorem composeDescend_hom {V : U.Etale} {W : X.Etale} (f : W ⟶ (smallEtaleCompose j).obj V) :
    (composeDescend j f).hom = f.left ≫ V.hom :=
  rfl

/-- The morphism of the small étale site of `U` underlying a morphism `f : W ⟶ j_* V` of the
small étale site of `X`, from `Stacks.EtaleCohomology.composeDescend`. -/
def composeDescendHom {V : U.Etale} {W : X.Etale} (f : W ⟶ (smallEtaleCompose j).obj V) :
    composeDescend j f ⟶ V :=
  MorphismProperty.Over.homMk f.left

/-- The morphism `composeDescendHom j f` has the same underlying morphism of schemes as `f`. -/
@[simp]
theorem composeDescendHom_left {V : U.Etale} {W : X.Etale}
    (f : W ⟶ (smallEtaleCompose j).obj V) : (composeDescendHom j f).left = f.left :=
  rfl

/-- Composition with `j` sends `Stacks.EtaleCohomology.composeDescend` back to the source of the
morphism it was built from. -/
def composeDescendIso {V : U.Etale} {W : X.Etale} (f : W ⟶ (smallEtaleCompose j).obj V) :
    (smallEtaleCompose j).obj (composeDescend j f) ≅ W :=
  MorphismProperty.Over.isoMk (Iso.refl _)
    ((Category.id_comp W.hom).trans
      ((MorphismProperty.Over.w f).symm.trans (Category.assoc f.left V.hom j).symm))

/-- The underlying morphism of schemes of `composeDescendIso j f` is the identity. -/
@[simp]
theorem composeDescendIso_hom_left {V : U.Etale} {W : X.Etale}
    (f : W ⟶ (smallEtaleCompose j).obj V) : (composeDescendIso j f).hom.left = 𝟙 W.left :=
  rfl

/-- The underlying morphism of schemes of the inverse of `composeDescendIso j f` is the
identity. -/
@[simp]
theorem composeDescendIso_inv_left {V : U.Etale} {W : X.Etale}
    (f : W ⟶ (smallEtaleCompose j).obj V) : (composeDescendIso j f).inv.left = 𝟙 W.left :=
  rfl

/-- A morphism of the small étale site of `U` with the same underlying morphism of schemes as
`f₂` gives back `f₂` after composing with `j` and the isomorphism `composeDescendIso j f₁`. -/
private theorem composeDescendIso_inv_comp_map {V V' : U.Etale} {W : X.Etale}
    (f₁ : W ⟶ (smallEtaleCompose j).obj V) (f₂ : W ⟶ (smallEtaleCompose j).obj V')
    (g : composeDescend j f₁ ⟶ V') (hg : g.left = f₂.left) :
    (composeDescendIso j f₁).inv ≫ (smallEtaleCompose j).map g = f₂ :=
  MorphismProperty.Over.Hom.ext ((Category.id_comp _).trans hg)

/-- Composition with an étale morphism preserves covering sieves of the small étale topology. -/
theorem smallEtaleCompose_coverPreserving :
    CoverPreserving (smallEtaleTopology U) (smallEtaleTopology X) (smallEtaleCompose j) where
  cover_preserve := by
    intro V S hS
    rw [Stacks.EtaleCohomology.mem_smallEtaleTopology_iff] at hS ⊢
    intro w
    obtain ⟨V', g, hg, hw⟩ := hS w
    exact ⟨(smallEtaleCompose j).obj V', (smallEtaleCompose j).map g,
      Sieve.image_mem_functorPushforward _ _ hg, hw⟩

/-- Composition with an étale morphism is compatible preserving. -/
theorem smallEtaleCompose_compatiblePreserving :
    CompatiblePreserving.{v} (smallEtaleTopology X) (smallEtaleCompose j) where
  compatible := by
    intro F Z T x hx V₁ V₂ W f₁ f₂ g₁ g₂ hg₁ hg₂ h
    have hl : f₁.left ≫ g₁.left = f₂.left ≫ g₂.left :=
      congrArg (fun k => (Scheme.Etale.forget X ⋙ CategoryTheory.Over.forget X).map k) h
    have hw : f₂.left ≫ V₂.hom = (composeDescend j f₁).hom :=
      (congrArg (fun k => f₂.left ≫ k) (MorphismProperty.Over.w g₂).symm).trans <|
        (Category.assoc f₂.left g₂.left Z.hom).symm.trans <|
          (congrArg (fun k => k ≫ Z.hom) hl.symm).trans <|
            (Category.assoc f₁.left g₁.left Z.hom).trans
              (congrArg (fun k => f₁.left ≫ k) (MorphismProperty.Over.w g₁))
    let g₁' : composeDescend j f₁ ⟶ V₁ := composeDescendHom j f₁
    let g₂' : composeDescend j f₁ ⟶ V₂ := MorphismProperty.Over.homMk f₂.left hw
    calc F.obj.map f₁.op (x g₁ hg₁)
        = F.obj.map ((composeDescendIso j f₁).inv ≫
            (smallEtaleCompose j).map g₁').op (x g₁ hg₁) := by
          rw [composeDescendIso_inv_comp_map j f₁ f₁ g₁' rfl]
      _ = F.obj.map (composeDescendIso j f₁).inv.op
            (F.obj.map ((smallEtaleCompose j).map g₁').op (x g₁ hg₁)) :=
          Functor.map_comp_apply F.obj _ _ _
      _ = F.obj.map (composeDescendIso j f₁).inv.op
            (F.obj.map ((smallEtaleCompose j).map g₂').op (x g₂ hg₂)) :=
          congrArg _ (hx g₁' g₂' hg₁ hg₂ (MorphismProperty.Over.Hom.ext hl))
      _ = F.obj.map ((composeDescendIso j f₁).inv ≫
            (smallEtaleCompose j).map g₂').op (x g₂ hg₂) :=
          (Functor.map_comp_apply F.obj _ _ _).symm
      _ = F.obj.map f₂.op (x g₂ hg₂) := by
          rw [composeDescendIso_inv_comp_map j f₁ f₂ g₂' rfl]

/-- Composition with an étale morphism is a continuous functor of small étale sites. -/
instance smallEtaleCompose_isContinuous :
    (smallEtaleCompose j).IsContinuous (smallEtaleTopology U) (smallEtaleTopology X) :=
  Functor.isContinuous_of_coverPreserving
    (smallEtaleCompose_compatiblePreserving j) (smallEtaleCompose_coverPreserving j)

/-- Composition with an étale morphism is a cocontinuous functor of small étale sites: a
covering sieve of `j_* V` pulls back to a covering sieve of `V`, because the arrows of the pulled
back sieve have the same images on underlying spaces. -/
instance smallEtaleCompose_isCocontinuous :
    (smallEtaleCompose j).IsCocontinuous (smallEtaleTopology U) (smallEtaleTopology X) where
  cover_lift := by
    intro V S hS
    rw [Stacks.EtaleCohomology.mem_smallEtaleTopology_iff] at hS ⊢
    intro w
    obtain ⟨W, h, hh, hw⟩ := hS w
    refine ⟨composeDescend j h, composeDescendHom j h, ?_, hw⟩
    have heq : (smallEtaleCompose j).map (composeDescendHom j h) =
        (composeDescendIso j h).hom ≫ h :=
      MorphismProperty.Over.Hom.ext (Category.id_comp h.left).symm
    change S.arrows ((smallEtaleCompose j).map (composeDescendHom j h))
    exact heq ▸ S.downward_closed hh (composeDescendIso j h).hom

/-- Composition with an étale morphism `j : U ⟶ X` is left adjoint to base change along `j`, as
functors between the small étale sites.  This is the site-level shadow of the adjunction
`j_! ⊣ j^{-1}` on sheaves. -/
def smallEtaleComposeBaseChangeAdj :
    smallEtaleCompose j ⊣ Stacks.EtaleCohomology.smallEtaleBaseChange j := by
  letI : MorphismProperty.HasPullbacksAlong (@Etale : MorphismProperty Scheme.{u}) j :=
    ⟨fun _ _ ↦ inferInstance⟩
  letI : MorphismProperty.IsStableUnderBaseChangeAlong
      (@Etale : MorphismProperty Scheme.{u}) j :=
    ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
  exact MorphismProperty.Over.mapPullbackAdj (@Etale) ⊤ j hj trivial

end AlgebraicGeometry.Scheme.Etale

namespace Stacks.EtaleCohomology

open AlgebraicGeometry.Scheme.Etale

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]

/-- The restriction functor `j^{-1} : Sh(X_étale) ⥤ Sh(U_étale)` on sheaves of sets of the small
étale sites of an étale morphism `j : U ⟶ X`.  On sections it is precomposition with
`AlgebraicGeometry.Scheme.Etale.smallEtaleCompose`: `(j^{-1} G)(V) = G(V)` for `V` étale over
`U`. -/
abbrev etaleRestrictionSets :
    Sheaf X.smallEtaleTopology (Type (max (u + 1) v)) ⥤
      Sheaf U.smallEtaleTopology (Type (max (u + 1) v)) :=
  (smallEtaleCompose j).sheafPushforwardContinuous
    (Type (max (u + 1) v)) U.smallEtaleTopology X.smallEtaleTopology

/-- **Stacks Project, Tag 03S3 (1).** Extension by zero `j_!^{Sh}` on sheaves of sets of the
small étale sites of an étale morphism `j : U ⟶ X`: the left adjoint of restriction, realised as
the sheafification of the left Kan extension along composition with `j`. -/
@[stacks 03S3 "sets: the left adjoint of restriction"]
abbrev extensionByZeroSets :
    Sheaf U.smallEtaleTopology (Type (max (u + 1) v)) ⥤
      Sheaf X.smallEtaleTopology (Type (max (u + 1) v)) :=
  Functor.sheafPullbackConstruction.sheafPullback (smallEtaleCompose j)
    (Type (max (u + 1) v)) U.smallEtaleTopology X.smallEtaleTopology

/-- **Stacks Project, Tag 03S3 (1).** Extension by zero is left adjoint to restriction, on
sheaves of sets. -/
@[stacks 03S3 "sets: the left adjoint of restriction"]
def extensionByZeroSetsAdj :
    extensionByZeroSets.{u, v} j ⊣ etaleRestrictionSets.{u, v} j :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _

/-- The restriction functor `j^{-1}` on abelian sheaves of the small étale sites of an étale
morphism `j : U ⟶ X`.  On sections it is precomposition with
`AlgebraicGeometry.Scheme.Etale.smallEtaleCompose`: `(j^{-1} G)(V) = G(V)` for `V` étale over
`U`. -/
abbrev etaleRestriction :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf U.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} :=
  (smallEtaleCompose j).sheafPushforwardContinuous
    AddCommGrpCat.{max (u + 1) v} U.smallEtaleTopology X.smallEtaleTopology

/-- The sections of `j^{-1} G` over an object `V` of the small étale site of `U` are the
sections of `G` over `V` regarded as a scheme étale over `X`. -/
theorem etaleRestriction_obj_val_obj
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (V : U.Etale) :
    ((etaleRestriction.{u, v} j).obj G).obj.obj (Opposite.op V) =
      G.obj.obj (Opposite.op ((smallEtaleCompose j).obj V)) :=
  rfl

/-- The direct image `j_*` on abelian sheaves of the small étale sites of an étale morphism
`j : U ⟶ X`: the right adjoint of restriction. -/
abbrev etaleDirectImage :
    Sheaf U.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} :=
  (smallEtaleCompose j).sheafPushforwardCocontinuous
    AddCommGrpCat.{max (u + 1) v} U.smallEtaleTopology X.smallEtaleTopology

/-- **Stacks Project, Tag 03S3 (2).** Extension by zero `j_!` on abelian sheaves of the small
étale sites of an étale morphism `j : U ⟶ X`: the left adjoint of restriction, realised as the
sheafification of the left Kan extension along composition with `j`. -/
@[stacks 03S3 "abelian: the left adjoint of restriction"]
abbrev extensionByZero [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}] :
    Sheaf U.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} :=
  Functor.sheafPullbackConstruction.sheafPullback (smallEtaleCompose j)
    AddCommGrpCat.{max (u + 1) v} U.smallEtaleTopology X.smallEtaleTopology

/-- **Stacks Project, Tag 03S3 (2).** Extension by zero is left adjoint to restriction, on
abelian sheaves. -/
@[stacks 03S3 "abelian: the left adjoint of restriction"]
def extensionByZeroAdj [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}] :
    extensionByZero.{u, v} j ⊣ etaleRestriction.{u, v} j :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _

/-- Restriction is left adjoint to the direct image. -/
def etaleDirectImageAdj : etaleRestriction.{u, v} j ⊣ etaleDirectImage.{u, v} j :=
  Functor.sheafAdjunctionCocontinuous _ _ _ _

/-- The characterising property of extension by zero: the functorial bijection
`Hom_X(j_! F, G) = Hom_U(F, j^{-1} G)` of Stacks Tag 03S3. -/
def extensionByZeroHomEquiv [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    ((extensionByZero.{u, v} j).obj F ⟶ G) ≃ (F ⟶ (etaleRestriction.{u, v} j).obj G) :=
  (extensionByZeroAdj.{u, v} j).homEquiv F G

end Stacks.EtaleCohomology

end
