module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionMorphismsAffine
public import StacksFrontier.Deformation.Artin.Versality

/-!
# Versality of a morphism out of a completion at a point

Let `S` be a scheme contained in a big fppf site `B`, let `V` be a scheme of the site, let
`Z ⊆ |V|` and let `g : V_{/Z} ⟶ W` be a morphism from the completion of `V` along `Z` (Stacks
0AMC) to an fppf sheaf `W`. For a point `v ∈ Z` with residue field `k`, the restrictions of `g`
to the infinitesimal neighbourhoods `Spec(𝒪_{V,v}/𝔪ⁿ)` form a formal object of `W`, and **Section
07XZ** calls `g` *versal at `v`* when that formal object is versal (Formal Deformation Theory,
Definition 06HR): the induced map from the functor of points of `𝒪^∧_{V,v}` on the category `𝒞_Λ`
of Artinian local `Λ`-algebras with residue field `k` to the predeformation functor of `W` at the
image of `v` is smooth.

## Main definitions

* `AlgebraicGeometry.FormalSpace.IsVersalAtCompletion`: versality of `g` at `v`.

## Implementation notes

The definition writes out the smoothness condition, exactly as
`Deformation.Artin.IsVersalAt` (Tag 07XF) does for an object over a scheme. The base `Λ` is the
local ring of `S` at the image of `v` and the residue field is the residue field of `V` at `v`,
with the algebra structure `Deformation.Artin.residueFieldAlgebra`; these are the base and residue
field of the predeformation category at `v`. A point of the functor of `𝒪^∧_{V,v}` over an
Artinian `A` is a local homomorphism `𝒪_{V,v} → A` compatible with the identifications of the
residue fields, that is a morphism `a : Spec A ⟶ V` over `S` whose restriction to the closed point
is the canonical `Spec k ⟶ V`; it lies in `V_{/Z}` as soon as `v ∈ Z`, through the section of the
completion it determines (`AlgebraicGeometry.FormalSpace.presheafSection`). Smoothness asks that
for a surjection `A' ⟶ A` in `𝒞_Λ`, every such `a` over `A` together with a section `z` of `W` over
`Spec A'` restricting to the image of `a` comes from some `b` over `A'` restricting to `a` and
mapping to `z`.

The objects `Spec A`, `Spec A'` and the closed immersion between them are taken in the site, as
in `Deformation.Artin.IsVersalAt`, since `W` is a sheaf on the site. The image condition of the
completion is part of the data of `a` and `b`; it holds automatically when `v ∈ Z`, since `Spec A`
is a one-point scheme mapping to `v`.

## References

* [Stacks Project, Tag 07XZ](https://stacks.math.columbia.edu/tag/07XZ)
* [Stacks Project, Tag 06HR](https://stacks.math.columbia.edu/tag/06HR)
* [Stacks Project, Tag 0GI9](https://stacks.math.columbia.edu/tag/0GI9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Section 07XZ, versality of `g : V_{/Z} ⟶ W` at a point `v`.** For every surjection
`A' ⟶ A` of Artinian local algebras over `Λ = 𝒪_{S,s}` with residue field `k = κ(v)`, realised by
objects `T`, `T'` of the site and a morphism `T ⟶ T'` over `Spec A ⟶ Spec A'`, every morphism
`a : T ⟶ V` restricting to the canonical point `Spec k ⟶ V` and lying in `V_{/Z}`, and every
section `z` of `W` over `T'` restricting to `g(a)`, there is a morphism `b : T' ⟶ V` lying in
`V_{/Z}`, extending `a`, with `g(b) = z`. -/
def IsVersalAtCompletion (V : BigFppfOver B S hS)
    (Z : Set (Space.points B S hS (yoneda.obj V))) (W : FppfSheaf B S hS)
    (g : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ W)
    (v : ((Over.post B.inclusion).obj V : Over S).left) : Prop :=
  let U : Over S := (Over.post B.inclusion).obj V
  letI : Algebra (S.presheaf.stalk (Deformation.Artin.basePoint U v)) (U.left.residueField v) :=
    Deformation.Artin.residueFieldAlgebra U v
  ∀ (A A' : Deformation.ArtinianLocalAlgCat.{u, u, u}
      (S.presheaf.stalk (Deformation.Artin.basePoint U v)) (U.left.residueField v))
    (f : A' ⟶ A), Function.Surjective f.hom →
    ∀ (T T' : BigFppfOver B S hS)
      (hT : (Over.post B.inclusion).obj T = Over.mk
        (Spec.map (CommRingCat.ofHom
          (algebraMap (S.presheaf.stalk (Deformation.Artin.basePoint U v)) A)) ≫
          S.fromSpecStalk (Deformation.Artin.basePoint U v)))
      (hT' : (Over.post B.inclusion).obj T' = Over.mk
        (Spec.map (CommRingCat.ofHom
          (algebraMap (S.presheaf.stalk (Deformation.Artin.basePoint U v)) A')) ≫
          S.fromSpecStalk (Deformation.Artin.basePoint U v)))
      (i : T ⟶ T'),
      eqToHom (congrArg Over.left hT).symm ≫ ((Over.post B.inclusion).map i).left ≫
          eqToHom (congrArg Over.left hT') =
        Spec.map (CommRingCat.ofHom f.hom.toRingHom) →
      ∀ (a : T ⟶ V) (ha : Space.HasImageIn B S hS (yoneda.obj V) Z T a),
        Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A)) ≫
            eqToHom (congrArg Over.left hT).symm ≫ ((Over.post B.inclusion).map a).left =
          U.left.fromSpecResidueField v →
        ∀ z : W.obj.obj (op T'),
          W.obj.map i.op z = g.hom.app (op T) (presheafSection B S hS a ha) →
          ∃ (b : T' ⟶ V) (hb : Space.HasImageIn B S hS (yoneda.obj V) Z T' b),
            i ≫ b = a ∧ g.hom.app (op T') (presheafSection B S hS b hb) = z

end AlgebraicGeometry.FormalSpace
