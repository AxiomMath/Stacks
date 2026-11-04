module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Formula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sheafification.SmallEtaleAbelian
import StacksCore.Tactic.StacksAttribute

/-!
# The sheafification of the direct-sum presheaf is left adjoint to restriction

Let `j : U ⟶ X` be an étale morphism of schemes.  Stacks Tag 0F4K defines a presheaf on the
small étale site of `X` by the direct-sum formula

```
(j_{p!} F)(V) = ⨁_{φ : V → U} F(V →^φ U)
```

the sum over the morphisms `φ : V ⟶ U` over `X` of the sections of `F` over `V` regarded as a
scheme étale over `U` through `φ`.  This file assembles that presheaf as a functor whose
sections are *literally* those direct sums, and shows that its sheafification is a left adjoint
of the restriction functor `j^{-1}`.  This is Stacks Tag 03S4.

## Main definitions

* `Stacks.EtaleCohomology.extensionByZeroDirectSumPresheaf`: the presheaf `j_{p!} F` of Stacks
  Tag 0F4K, with `(j_{p!} F)(V)` the direct sum `⨁_{φ : V → U} F(V →^φ U)` itself.
* `Stacks.EtaleCohomology.extensionByZeroDirectSum`: the same construction as a functor
  `j_{p!}` on abelian presheaves.
* `AlgebraicGeometry.Scheme.Etale.sourceDescendMap`: the morphism of the small étale site of
  `U` along which the `φ`-th summand is transported by a morphism `g : W ⟶ V` over `X`.

## Main results

* `Stacks.EtaleCohomology.extensionByZeroDirectSumPresheaf_obj` and
  `Stacks.EtaleCohomology.ι_comp_extensionByZeroDirectSumPresheaf_map`: the sections of
  `j_{p!} F` over `V` are the direct sum of the groups `F(V →^φ U)`, and the restriction map
  along `g : W ⟶ V` takes the `φ`-th summand to the `(g ≫ φ)`-th summand by the map `F` assigns
  to `g`.
* `Stacks.EtaleCohomology.extensionByZeroDirectSumAdj`: **Stacks Tag 03S4**, the sheafification
  of `j_{p!}` is a left adjoint of `j^{-1}` on abelian sheaves of the small étale sites.

## Implementation notes

`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Formula` identifies the left Kan
extension of `F` along composition with `j` with the direct sums summand by summand
(`Stacks.EtaleCohomology.extensionByZeroPresheafSectionIso`), but leaves the direct sums
themselves assembled into a presheaf only through that identification.  The presheaf here is
`CategoryTheory.Functor.copyObj` of the left Kan extension along those isomorphisms, so that its
sections over `V` are the direct sum on the nose, and
`ι_comp_extensionByZeroDirectSumPresheaf_map` checks that its restriction maps are the evident
ones; together those two facts pin the presheaf down to the one Stacks Tag 0F4K writes.

The adjunction is then the adjunction `j_! ⊣ j^{-1}` of
`Stacks.EtaleCohomology.extensionByZeroAdj` transported along the isomorphism of left adjoints,
since `Stacks.EtaleCohomology.extensionByZero` is by construction the sheafification of the left
Kan extension (`Stacks.EtaleCohomology.extensionByZero_obj_eq_sheafify`).  Sheafification of
abelian presheaves on the small étale site is available at the coefficient universe
`max (u + 1) v` by `AlgebraicGeometry.Scheme.hasSheafify_smallEtaleTopology`, so the adjunction
below is stated for an arbitrary étale morphism of schemes with no further input.

## References

* [Stacks Project, Tag 03S4](https://stacks.math.columbia.edu/tag/03S4)
* [Stacks Project, Tag 0F4K](https://stacks.math.columbia.edu/tag/0F4K)
* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe w₂ w₁ u v

attribute [local instance] AlgebraicGeometry.Etale.isStableUnderComposition
attribute [local instance] AlgebraicGeometry.Etale.instIsMultiplicativeScheme

namespace AlgebraicGeometry.Scheme.Etale

variable {U X : Scheme.{u}} (j : U ⟶ X) [hj : Etale j]

/-- The morphism of the small étale site of `U` from `W →^{g ≫ φ} U` to `V →^φ U` underlying a
morphism `g : W ⟶ V` of the small étale site of `X`: the index `φ : V ⟶ U` of a summand of the
formula of Stacks Tag 0F4K pulls back along `g` to the index `g ≫ φ`, and the two summands are
the sections of a presheaf at the ends of this morphism. -/
def sourceDescendMap {V W : X.Etale} (g : W ⟶ V) (φ : V ⟶ smallEtaleSource j) :
    sourceDescend j (g ≫ φ) ⟶ sourceDescend j φ :=
  MorphismProperty.Over.homMk g.left rfl

/-- The underlying morphism of schemes of `sourceDescendMap j g φ` is that of `g`. -/
@[simp]
theorem sourceDescendMap_left {V W : X.Etale} (g : W ⟶ V) (φ : V ⟶ smallEtaleSource j) :
    (sourceDescendMap j g φ).left = g.left :=
  rfl

/-- The identifications of `AlgebraicGeometry.Scheme.Etale.sourceDescendIso` are natural: going
down to the summand indexed by `g ≫ φ` and across to the one indexed by `φ` agrees with going
across by `g` and down. -/
theorem comp_sourceDescendIso_inv {V W : X.Etale} (g : W ⟶ V) (φ : V ⟶ smallEtaleSource j) :
    g ≫ (sourceDescendIso j φ).inv =
      (sourceDescendIso j (g ≫ φ)).inv ≫ (smallEtaleCompose j).map (sourceDescendMap j g φ) :=
  MorphismProperty.Over.Hom.ext ((Category.comp_id g.left).trans (Category.id_comp g.left).symm)

end AlgebraicGeometry.Scheme.Etale

namespace Stacks.EtaleCohomology

open AlgebraicGeometry.Scheme.Etale

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
  {A : Type w₁} [Category.{w₂} A]
  [∀ F : (U.Etale)ᵒᵖ ⥤ A, (smallEtaleCompose j).op.HasPointwiseLeftKanExtension F]

/-- The summand inclusions of the formula of Stacks Tag 0F4K are compatible with the restriction
maps of `j_{p!} F`: restricting the `φ`-th summand of the sections over `V` along a morphism
`g : W ⟶ V` over `X` lands in the `(g ≫ φ)`-th summand of the sections over `W`, through the map
that `F` assigns to `AlgebraicGeometry.Scheme.Etale.sourceDescendMap`. -/
theorem extensionByZeroSummandInclusion_comp_map
    (F : (U.Etale)ᵒᵖ ⥤ A) {V W : X.Etale} (g : W ⟶ V) (φ : V ⟶ smallEtaleSource j) :
    extensionByZeroSummandInclusion j F φ ≫ (extensionByZeroPresheaf j F).map g.op =
      F.map (sourceDescendMap j g φ).op ≫ extensionByZeroSummandInclusion j F (g ≫ φ) := by
  have hnat : F.map (sourceDescendMap j g φ).op ≫
      ((smallEtaleCompose j).op.lanUnit.app F).app (op (sourceDescend j (g ≫ φ))) =
      ((smallEtaleCompose j).op.lanUnit.app F).app (op (sourceDescend j φ)) ≫
        (extensionByZeroPresheaf j F).map
          ((smallEtaleCompose j).map (sourceDescendMap j g φ)).op :=
    ((smallEtaleCompose j).op.lanUnit.app F).naturality (sourceDescendMap j g φ).op
  simp only [extensionByZeroSummandInclusion]
  rw [Category.assoc, ← Functor.map_comp, ← op_comp, comp_sourceDescendIso_inv j g φ, op_comp,
    Functor.map_comp, ← Category.assoc, ← hnat, Category.assoc]

variable [HasCoproducts.{u} A]

/-- The presheaf `j_{p!} F` of Stacks Tag 0F4K, with its sections over a scheme `V` étale over
`X` the direct sum `⨁_{φ : V → U} F(V →^φ U)` itself: the left Kan extension of `F` along
composition with `j`, with its sections replaced by the direct sums they are identified with in
`Stacks.EtaleCohomology.extensionByZeroPresheafSectionIso`. -/
def extensionByZeroDirectSumPresheaf (F : (U.Etale)ᵒᵖ ⥤ A) : (X.Etale)ᵒᵖ ⥤ A :=
  (extensionByZeroPresheaf j F).copyObj
    (fun V => ∐ fun φ : V.unop ⟶ smallEtaleSource j => F.obj (op (sourceDescend j φ)))
    (fun V => (extensionByZeroPresheafSectionIso j F V.unop).symm)

/-- **Stacks Project, Tag 0F4K.** The sections of `j_{p!} F` over a scheme `V` étale over `X`
are the direct sum, over the morphisms `φ : V ⟶ U` over `X`, of the sections of `F` over `V`
regarded as étale over `U` through `φ`. -/
theorem extensionByZeroDirectSumPresheaf_obj (F : (U.Etale)ᵒᵖ ⥤ A) (V : X.Etale) :
    (extensionByZeroDirectSumPresheaf j F).obj (op V) =
      ∐ fun φ : V ⟶ smallEtaleSource j => F.obj (op (sourceDescend j φ)) :=
  rfl

/-- The restriction maps of `j_{p!} F` are the evident ones: a morphism `g : W ⟶ V` over `X`
takes the summand indexed by `φ : V ⟶ U` into the summand indexed by `g ≫ φ`, through the map
that `F` assigns to `AlgebraicGeometry.Scheme.Etale.sourceDescendMap`. -/
theorem ι_comp_extensionByZeroDirectSumPresheaf_map (F : (U.Etale)ᵒᵖ ⥤ A) {V W : X.Etale}
    (g : W ⟶ V) (φ : V ⟶ smallEtaleSource j) :
    Sigma.ι (fun ψ : V ⟶ smallEtaleSource j => F.obj (op (sourceDescend j ψ))) φ ≫
        (extensionByZeroDirectSumPresheaf j F).map g.op =
      F.map (sourceDescendMap j g φ).op ≫
        Sigma.ι (fun ψ : W ⟶ smallEtaleSource j => F.obj (op (sourceDescend j ψ))) (g ≫ φ) := by
  have hι : ∀ {Y : X.Etale} (ψ : Y ⟶ smallEtaleSource j),
      Sigma.ι (fun χ : Y ⟶ smallEtaleSource j => F.obj (op (sourceDescend j χ))) ψ ≫
        (extensionByZeroPresheafSectionIso j F Y).hom = extensionByZeroSummandInclusion j F ψ :=
    fun ψ => Sigma.ι_desc (fun χ => extensionByZeroSummandInclusion j F χ) ψ
  show _ ≫ ((extensionByZeroPresheafSectionIso j F V).hom ≫
    (extensionByZeroPresheaf j F).map g.op ≫
    (extensionByZeroPresheafSectionIso j F W).inv) = _
  rw [← Category.assoc, hι, ← Category.assoc,
    extensionByZeroSummandInclusion_comp_map j F g φ, Category.assoc, ← hι, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- The presheaf-level extension by zero `j_{p!}` of Stacks Tag 0F4K as a functor on abelian
presheaves: on `F` it is the presheaf whose sections over `V` are `⨁_{φ : V → U} F(V →^φ U)`. -/
def extensionByZeroDirectSum : ((U.Etale)ᵒᵖ ⥤ A) ⥤ ((X.Etale)ᵒᵖ ⥤ A) :=
  (smallEtaleCompose j).op.lan.copyObj (extensionByZeroDirectSumPresheaf j)
    fun _ => Functor.isoCopyObj _ _ _

/-- The functor `j_{p!}` sends `F` to the presheaf with sections
`⨁_{φ : V → U} F(V →^φ U)`. -/
theorem extensionByZeroDirectSum_obj (F : (U.Etale)ᵒᵖ ⥤ A) :
    (extensionByZeroDirectSum j).obj F = extensionByZeroDirectSumPresheaf j F :=
  rfl

/-- The left Kan extension along composition with `j` is the functor `j_{p!}` of Stacks Tag
0F4K. -/
def lanIsoExtensionByZeroDirectSum :
    (smallEtaleCompose j).op.lan ≅ extensionByZeroDirectSum.{w₂, w₁, u} j (A := A) :=
  Functor.isoCopyObj _ _ _

end Stacks.EtaleCohomology

namespace Stacks.EtaleCohomology

open AlgebraicGeometry.Scheme.Etale

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]

/-- **Stacks Project, Tag 03S4.** Extension by zero, defined as the sheafification of the
presheaf `j_{p!}` whose sections over a scheme `V` étale over `X` are the direct sum
`⨁_{φ : V → U} F(V →^φ U)` of Stacks Tag 0F4K, is a left adjoint of the restriction functor
`j^{-1}` on abelian sheaves of the small étale sites of an étale morphism `j : U ⟶ X` of
schemes. -/
@[stacks 03S4 "the sheafification of the direct-sum presheaf j_{p!} is a left adjoint of j^{-1}"]
def extensionByZeroDirectSumAdj :
    sheafToPresheaf U.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⋙
        extensionByZeroDirectSum j (A := AddCommGrpCat.{max (u + 1) v}) ⋙
        presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⊣
      etaleRestriction.{u, v} j :=
  Adjunction.ofNatIsoLeft (extensionByZeroAdj.{u, v} j)
    (Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight (lanIsoExtensionByZeroDirectSum j) _))

end Stacks.EtaleCohomology

end

