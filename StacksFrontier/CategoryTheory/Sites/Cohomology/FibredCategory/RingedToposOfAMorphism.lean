module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Relocalization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingForget
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHomComp
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.OneMorphismContinuity
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.RingedToposOfAFibredCategory
import StacksCore.Tactic.StacksAttribute

/-!
# A morphism of fibred categories over a ringed site

Let `(D, O_D)` be a ringed site, let `p : C ⥤ D` and `p' : C' ⥤ D` be fibred categories over its
underlying site, and let `u : C' ⥤ C` be a 1-morphism of fibred categories over `D`
(Stacks 02XP). Give `C` and `C'` the topologies they inherit from `D` (Stacks 06NV). Stacks 06NW
then provides morphisms of topoi `π : Sh(C) ⟶ Sh(D)`, `π' : Sh(C') ⟶ Sh(D)` and
`g : Sh(C') ⟶ Sh(C)`, and setting `O_C = π⁻¹O_D`, `O_{C'} = (π')⁻¹O_D` makes

```
(Sh(C'), O_{C'}) --g--> (Sh(C), O_C)
         \                 /
          π'             π
            \           /
            (Sh(D), O_D)
```

a commutative diagram of ringed topoi, because `g⁻¹O_C = O_{C'}`.

## Main definitions

* `Stacks.Sites.FibredCategory.MorphismSituation`: the standing data of Stacks 08PA.
* `Stacks.Sites.FibredCategory.MorphismSituation.baseTopos`, `.totalTopos`, `.sourceTopos`: the
  three ringed topoi.
* `Stacks.Sites.FibredCategory.MorphismSituation.toBase`, `.sourceToBase`: the two morphisms of
  ringed topoi to the base.
* `Stacks.Sites.FibredCategory.MorphismSituation.RingedToposDiagram`: the induced geometric maps
  and the commutative diagram of ringed topoi, with every map pinned by an equation rather than
  asserted to exist.
`MorphismSituation.ringedToposDiagram`, the construction of a term of that structure at a
concrete situation, is **not in this file**. Twenty-three of the twenty-four fields' witnesses
are proved here and the `commutes` chain reduces to a single projection defeq
(`S.baseTopos.J ≡ S.base.J`) that exceeds the default heartbeat budget five different ways; see
the implementation notes. `pi'OverBaseTopos`, `unit_comp_mate_baseTopos`,
`sourceToBase_fSharp_baseTopos` and the three `HasSheafCompose` instances at `S.baseTopos.J` are
provided so that a construction of the full diagram starts at that one line. This list does not
provide a `ringedToposDiagram` declaration.

## Implementation notes

The continuity and cocontinuity of `u` are
`CategoryTheory.Functor.IsFibredOneMorphism.isContinuous_inheritedTopology` and
`.isCocontinuous_inheritedTopology`, which assume nothing of the base beyond its topology; the
form of Stacks 06NW in
`CategoryTheory.Functor.IsFibredOneMorphism.isContinuous_and_isCocontinuous_inheritedTopology`
cannot be used here, as it assumes `HasPullbacks` on the base and a ringed site has no fibre
products.

## References

* [Stacks Project, Tag 08PA](https://stacks.math.columbia.edu/tag/08PA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u₀ u₁ u₂ v₀ v₁ v₂ w ua ub va vb ww


namespace CategoryTheory.Functor

/-- The morphism of topoi attached to a functor of sites that is both continuous and
cocontinuous (Stacks 00XO): its inverse image is restriction along `F.op` and its direct image is
the right Kan extension along `F.op`.

Each field is a single application, so that projecting out of it stays cheap: an inline proof of
left exactness here makes every later unification that has to see through this definition
expensive. Left exactness is the instance
`CategoryTheory.Functor.preservesFiniteLimits_sheafPushforwardContinuous` (Stacks 04J4). -/
@[stacks 00XO "for a functor that is also continuous, with inverse image the restriction
  along F.op",
  sga "4 III 2.3" "special case",
  sga "4 III 2.4" "partial",
  sga "4 IV 4.6.1" "more general",
  sga "4 IV 4.7" "special case",
  sga "4 IV 4.9.1"]
noncomputable def morphismOfTopoiOfCocontinuous {A : Type ua}
    [Category.{va} A] {B : Type ub} [Category.{vb} B]
    (F : A ⥤ B) (JA : GrothendieckTopology A) (JB : GrothendieckTopology B)
    [F.IsContinuous JA JB] [F.IsCocontinuous JA JB]
    [∀ (G : Aᵒᵖ ⥤ Type ww), F.op.HasPointwiseRightKanExtension G] :
    MorphismOfTopoi (Sheaf JA (Type ww)) (Sheaf JB (Type ww)) where
  pushforward := F.sheafPushforwardCocontinuous (Type ww) JA JB
  inverseImage := F.sheafPushforwardContinuous (Type ww) JA JB
  adj := F.sheafAdjunctionCocontinuous (Type ww) JA JB
  preservesFiniteLimits := inferInstance

section Projections

variable {A : Type ua} [Category.{va} A] {B : Type ub} [Category.{vb} B]
  (F : A ⥤ B) (JA : GrothendieckTopology A) (JB : GrothendieckTopology B)
  [F.IsContinuous JA JB] [F.IsCocontinuous JA JB]
  [∀ (G : Aᵒᵖ ⥤ Type ww), F.op.HasPointwiseRightKanExtension G]

/-- The inverse image of `morphismOfTopoiOfCocontinuous` is restriction along `F.op`. -/
@[simp] theorem morphismOfTopoiOfCocontinuous_inverseImage :
    (morphismOfTopoiOfCocontinuous F JA JB).inverseImage =
      F.sheafPushforwardContinuous (Type ww) JA JB :=
  rfl

/-- The direct image of `morphismOfTopoiOfCocontinuous` is the right Kan extension along
`F.op`. -/
@[simp] theorem morphismOfTopoiOfCocontinuous_pushforward :
    (morphismOfTopoiOfCocontinuous F JA JB).pushforward =
      F.sheafPushforwardCocontinuous (Type ww) JA JB :=
  rfl

/-- The adjunction of `morphismOfTopoiOfCocontinuous` is the canonical one. -/
@[simp] theorem morphismOfTopoiOfCocontinuous_adj :
    (morphismOfTopoiOfCocontinuous F JA JB).adj =
      F.sheafAdjunctionCocontinuous (Type ww) JA JB :=
  rfl

end Projections

end CategoryTheory.Functor

namespace Stacks.Sites.FibredCategory

/-- **Stacks 08PA, standing data.** A ringed site `(D, O_D)`, two fibred categories over its
underlying site, and a 1-morphism of fibred categories between them. -/
@[stacks 08PA "standing data"]
structure MorphismSituation.{a₀, a₁, a₂, b₀, b₁, b₂, c} where
  /-- The ringed base site. -/
  base : AlgebraicGeometry.RingedSite.{a₀, b₀, c}
  /-- The target fibred category. -/
  total : Type a₁
  /-- Morphisms of the target fibred category. -/
  [totalCategory : Category.{b₁} total]
  /-- The source fibred category. -/
  source : Type a₂
  /-- Morphisms of the source fibred category. -/
  [sourceCategory : Category.{b₂} source]
  /-- The target's structure functor. -/
  p : total ⥤ base.C
  /-- The source's structure functor. -/
  p' : source ⥤ base.C
  /-- The 1-morphism over the base. -/
  u : source ⥤ total
  /-- The target's structure functor is a fibred category. -/
  [pFibered : p.IsFibered]
  /-- The source's structure functor is a fibred category. -/
  [p'Fibered : p'.IsFibered]
  /-- `u` is a 1-morphism of fibred categories over the base. -/
  isFibredOneMorphism : p'.IsFibredOneMorphism p u

attribute [instance] MorphismSituation.totalCategory MorphismSituation.sourceCategory
  MorphismSituation.pFibered MorphismSituation.p'Fibered

namespace MorphismSituation

section Topologies

variable (S : MorphismSituation.{u₀, u₁, u₂, v₀, v₁, v₂, ww})

/-- The topology on the target fibred category inherited from the base site. -/
abbrev totalTopology : GrothendieckTopology S.total := S.p.inheritedTopology S.base.J

/-- The topology on the source fibred category inherited from the base site. -/
abbrev sourceTopology : GrothendieckTopology S.source := S.p'.inheritedTopology S.base.J

/-- The target's structure functor is continuous for the inherited topologies. -/
instance pContinuous : S.p.IsContinuous S.totalTopology S.base.J :=
  isContinuous_inheritedTopology_of_isFibered S.p S.base.J

/-- The target's structure functor is cocontinuous for the inherited topologies. -/
instance pCocontinuous : S.p.IsCocontinuous S.totalTopology S.base.J :=
  isCocontinuous_inheritedTopology_of_isFibered S.p S.base.J

/-- The source's structure functor is continuous for the inherited topologies. -/
instance p'Continuous : S.p'.IsContinuous S.sourceTopology S.base.J :=
  isContinuous_inheritedTopology_of_isFibered S.p' S.base.J

/-- The source's structure functor is cocontinuous for the inherited topologies. -/
instance p'Cocontinuous : S.p'.IsCocontinuous S.sourceTopology S.base.J :=
  isCocontinuous_inheritedTopology_of_isFibered S.p' S.base.J

/-- The 1-morphism is continuous for the two inherited topologies (Stacks 06NW). -/
instance uContinuous : S.u.IsContinuous S.sourceTopology S.totalTopology :=
  CategoryTheory.Functor.IsFibredOneMorphism.isContinuous_inheritedTopology S.base.J
    S.isFibredOneMorphism

/-- The 1-morphism is cocontinuous for the two inherited topologies (Stacks 06NW). -/
instance uCocontinuous : S.u.IsCocontinuous S.sourceTopology S.totalTopology :=
  CategoryTheory.Functor.IsFibredOneMorphism.isCocontinuous_inheritedTopology S.base.J
    S.isFibredOneMorphism

end Topologies

section Diagram

variable (S : MorphismSituation.{u₀, u₁, u₂, v₀, v₁, v₂, max w u₀ u₁ u₂ v₀ v₁ v₂})

/-- Composition with the forgetful functor preserves sheaves of rings on the base site.
Registered as an instance so that later statements do not re-solve it. -/
instance hasSheafComposeForgetRingBase :
    S.base.J.HasSheafCompose (forget RingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) :=
  inferInstance

/-- Composition with the forgetful functor to rings preserves sheaves of commutative rings on the
base site. -/
instance hasSheafComposeForget₂Base :
    S.base.J.HasSheafCompose
      (forget₂ CommRingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} RingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) :=
  inferInstance

/-- Composition with the forgetful functor preserves sheaves of commutative rings on the base
site. -/
instance hasSheafComposeForgetCommRingBase :
    S.base.J.HasSheafCompose (forget CommRingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) :=
  inferInstance

/-- Composition with the forgetful functor preserves sheaves of rings on the target site.
Registered so that later statements do not re-solve it. -/
instance hasSheafComposeForgetRingTotal :
    S.totalTopology.HasSheafCompose (forget RingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) :=
  inferInstance

/-- Composition with the forgetful functor to rings preserves sheaves of commutative rings on the
target site. -/
instance hasSheafComposeForget₂Total :
    S.totalTopology.HasSheafCompose
      (forget₂ CommRingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} RingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) :=
  inferInstance

/-- Composition with the forgetful functor preserves sheaves of commutative rings on the target
site. -/
instance hasSheafComposeForgetCommRingTotal :
    S.totalTopology.HasSheafCompose (forget CommRingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) :=
  inferInstance

/-- Composition with the forgetful functor preserves sheaves of rings on the source site.
Registered so that later statements do not re-solve it. -/
instance hasSheafComposeForgetRingSource :
    S.sourceTopology.HasSheafCompose (forget RingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) :=
  inferInstance

/-- Composition with the forgetful functor to rings preserves sheaves of commutative rings on the
source site. -/
instance hasSheafComposeForget₂Source :
    S.sourceTopology.HasSheafCompose
      (forget₂ CommRingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} RingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) :=
  inferInstance

/-- Composition with the forgetful functor preserves sheaves of commutative rings on the source
site. -/
instance hasSheafComposeForgetCommRingSource :
    S.sourceTopology.HasSheafCompose (forget CommRingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) :=
  inferInstance

/-- The morphism of topoi `π : Sh(C) ⟶ Sh(D)` of Stacks 06NW attached to the target. -/
noncomputable def pi :
    MorphismOfTopoi (Sheaf S.totalTopology (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))
      (Sheaf S.base.J (Type (max w u₀ u₁ u₂ v₀ v₁ v₂))) :=
  CategoryTheory.Functor.morphismOfTopoiOfCocontinuous.{_, _, _, _,
    max w u₀ u₁ u₂ v₀ v₁ v₂} S.p S.totalTopology S.base.J

/-- The morphism of topoi `π' : Sh(C') ⟶ Sh(D)` of Stacks 06NW attached to the source. -/
noncomputable def pi' :
    MorphismOfTopoi (Sheaf S.sourceTopology (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))
      (Sheaf S.base.J (Type (max w u₀ u₁ u₂ v₀ v₁ v₂))) :=
  CategoryTheory.Functor.morphismOfTopoiOfCocontinuous.{_, _, _, _,
    max w u₀ u₁ u₂ v₀ v₁ v₂} S.p' S.sourceTopology S.base.J

/-- The morphism of topoi `g : Sh(C') ⟶ Sh(C)` of Stacks 06NW attached to the 1-morphism. -/
noncomputable def g :
    MorphismOfTopoi (Sheaf S.sourceTopology (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))
      (Sheaf S.totalTopology (Type (max w u₀ u₁ u₂ v₀ v₁ v₂))) :=
  CategoryTheory.Functor.morphismOfTopoiOfCocontinuous.{_, _, _, _,
    max w u₀ u₁ u₂ v₀ v₁ v₂} S.u S.sourceTopology S.totalTopology

/-- The inverse image of `pi` is restriction along `p`. Stated at the situation, so that it
rewrites `S.pi.inverseImage` without unfolding `pi` to the underlying construction. -/
@[simp] theorem pi_inverseImage : S.pi.inverseImage =
    S.p.sheafPushforwardContinuous (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)) S.totalTopology S.base.J :=
  rfl

/-- The direct image of `pi` is the right Kan extension along `p`. -/
@[simp] theorem pi_pushforward : S.pi.pushforward =
    S.p.sheafPushforwardCocontinuous (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)) S.totalTopology S.base.J :=
  rfl

/-- The inverse image of `pi'` is restriction along `p'`. -/
@[simp] theorem pi'_inverseImage : S.pi'.inverseImage =
    S.p'.sheafPushforwardContinuous (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)) S.sourceTopology S.base.J :=
  rfl

/-- The direct image of `pi'` is the right Kan extension along `p'`. -/
@[simp] theorem pi'_pushforward : S.pi'.pushforward =
    S.p'.sheafPushforwardCocontinuous (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)) S.sourceTopology
      S.base.J :=
  rfl

/-- The inverse image of `g` is restriction along `u`. -/
@[simp] theorem g_inverseImage : S.g.inverseImage =
    S.u.sheafPushforwardContinuous (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)) S.sourceTopology
      S.totalTopology :=
  rfl

/-- The direct image of `g` is the right Kan extension along `u`. -/
@[simp] theorem g_pushforward : S.g.pushforward =
    S.u.sheafPushforwardCocontinuous (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)) S.sourceTopology
      S.totalTopology :=
  rfl

/-- The inverse image of `pi` preserves finite products. Registered as an instance so that later
statements do not have to unfold `pi` to find it. -/
instance preservesFiniteProductsInverseImagePi :
    PreservesFiniteProducts S.pi.inverseImage := inferInstance

/-- The direct image of `pi` preserves finite products. -/
instance preservesFiniteProductsPushforwardPi :
    PreservesFiniteProducts S.pi.pushforward := inferInstance

/-- The inverse image of `pi'` preserves finite products. Registered as an instance so that later
statements do not have to unfold `pi'` to find it. -/
instance preservesFiniteProductsInverseImagePi' :
    PreservesFiniteProducts S.pi'.inverseImage := inferInstance

/-- The direct image of `pi'` preserves finite products. -/
instance preservesFiniteProductsPushforwardPi' :
    PreservesFiniteProducts S.pi'.pushforward := inferInstance

/-- The inverse image of `g` preserves finite products. Registered as an instance so that later
statements do not have to unfold `g` to find it. -/
instance preservesFiniteProductsInverseImageG :
    PreservesFiniteProducts S.g.inverseImage := inferInstance

/-- The direct image of `g` preserves finite products. -/
instance preservesFiniteProductsPushforwardG :
    PreservesFiniteProducts S.g.pushforward := inferInstance

/-- The base ringed topos `(Sh(D), O_D)`. -/
noncomputable def baseTopos :
    AlgebraicGeometry.RingedTopos.{v₀, u₀, max w u₀ u₁ u₂ v₀ v₁ v₂} where
  C := S.base.C
  J := S.base.J
  O := S.base.O

/-- The target ringed topos `(Sh(C), π⁻¹O_D)`. -/
noncomputable def totalTopos
    (π : MorphismOfTopoi
      (Sheaf S.totalTopology (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))
      (Sheaf S.base.J (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))) :
    AlgebraicGeometry.RingedTopos.{v₁, u₁, max w u₀ u₁ u₂ v₀ v₁ v₂} where
  C := S.total
  J := S.totalTopology
  O := (inverseImageCommRingFunctor π).obj S.base.O

/-- The source ringed topos `(Sh(C'), (π')⁻¹O_D)`. -/
noncomputable def sourceTopos
    (π' : MorphismOfTopoi
      (Sheaf S.sourceTopology (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))
      (Sheaf S.base.J (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))) :
    AlgebraicGeometry.RingedTopos.{v₂, u₂, max w u₀ u₁ u₂ v₀ v₁ v₂} where
  C := S.source
  J := S.sourceTopology
  O := (inverseImageCommRingFunctor π').obj S.base.O

/-- Composition with the forgetful functor preserves sheaves of rings on the base ringed topos.
Registered separately from the instance for `S.base.J`: instance search does not see through the
projection, so a consumer that speaks of `S.baseTopos.J` would re-derive it. -/
instance hasSheafComposeForgetRingBaseTopos :
    S.baseTopos.J.HasSheafCompose (forget RingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) :=
  inferInstance

/-- Composition with the forgetful functor to rings preserves sheaves of commutative rings on the
base ringed topos. -/
instance hasSheafComposeForget₂BaseTopos :
    S.baseTopos.J.HasSheafCompose
      (forget₂ CommRingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} RingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) :=
  inferInstance

/-- Composition with the forgetful functor preserves sheaves of commutative rings on the base
ringed topos. -/
instance hasSheafComposeForgetCommRingBaseTopos :
    S.baseTopos.J.HasSheafCompose (forget CommRingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) :=
  inferInstance

/-- `π'`, with its target topos spelled through the base *ringed topos*. The two spellings are
definitionally equal; naming the coercion once, here, means no consumer has to discharge it. -/
noncomputable abbrev pi'OverBaseTopos :
    MorphismOfTopoi (Sheaf S.sourceTopology (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))
      (Sheaf S.baseTopos.J (Type (max w u₀ u₁ u₂ v₀ v₁ v₂))) :=
  S.pi'

/-- The site of the base ringed topos. -/
theorem baseTopos_J : S.baseTopos.J = S.base.J := rfl

/-- The structure sheaf of the base ringed topos. -/
@[simp] theorem baseTopos_O : S.baseTopos.O = S.base.O := rfl

/-- The site of the target ringed topos. -/
theorem totalTopos_J
    (π : MorphismOfTopoi
      (Sheaf S.totalTopology (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))
      (Sheaf S.base.J (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))) :
    (S.totalTopos π).J = S.totalTopology := rfl

/-- The structure sheaf of the target ringed topos. -/
@[simp] theorem totalTopos_O
    (π : MorphismOfTopoi
      (Sheaf S.totalTopology (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))
      (Sheaf S.base.J (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))) :
    (S.totalTopos π).O = (inverseImageCommRingFunctor π).obj S.base.O := rfl

/-- The site of the source ringed topos. -/
theorem sourceTopos_J
    (π' : MorphismOfTopoi
      (Sheaf S.sourceTopology (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))
      (Sheaf S.base.J (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))) :
    (S.sourceTopos π').J = S.sourceTopology := rfl

/-- The structure sheaf of the source ringed topos. -/
@[simp] theorem sourceTopos_O
    (π' : MorphismOfTopoi
      (Sheaf S.sourceTopology (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))
      (Sheaf S.base.J (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))) :
    (S.sourceTopos π').O = (inverseImageCommRingFunctor π').obj S.base.O := rfl

/-- The canonical morphism of ringed topoi `(Sh(C), π⁻¹O_D) ⟶ (Sh(D), O_D)` attached to a
geometric morphism to the base: its structure map is the unit of the adjunction on sheaves of
commutative rings. -/
noncomputable def toBase
    (π : MorphismOfTopoi
      (Sheaf S.totalTopology (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))
      (Sheaf S.base.J (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))) :
    AlgebraicGeometry.RingedToposHom (S.totalTopos π) S.baseTopos where
  toToposHom := π
  fSharp := (commRingImageAdjunction π).unit.app S.base.O

/-- The analogous canonical morphism of ringed topoi `(Sh(C'), (π')⁻¹O_D) ⟶ (Sh(D), O_D)`. -/
noncomputable def sourceToBase
    (π' : MorphismOfTopoi
      (Sheaf S.sourceTopology (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))
      (Sheaf S.base.J (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))) :
    AlgebraicGeometry.RingedToposHom (S.sourceTopos π') S.baseTopos where
  toToposHom := π'
  fSharp := (commRingImageAdjunction π').unit.app S.base.O

/-- The functor forgetting the ring operations on the base ringed topos. -/
@[simp] theorem baseTopos_forgetRing :
    S.baseTopos.forgetRing =
      sheafCompose S.base.J (forget CommRingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) := rfl

/-- The underlying morphism of topoi of the canonical morphism to the base. -/
@[simp] theorem toBase_toToposHom (π : MorphismOfTopoi
      (Sheaf S.totalTopology (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))
      (Sheaf S.base.J (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))) :
    (S.toBase π).toToposHom = π := rfl

/-- The structure map of the canonical morphism to the base is the unit of the adjunction. -/
@[simp] theorem toBase_fSharp (π : MorphismOfTopoi
      (Sheaf S.totalTopology (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))
      (Sheaf S.base.J (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))) :
    (S.toBase π).fSharp = (commRingImageAdjunction π).unit.app S.base.O := rfl

/-- The underlying morphism of topoi of the canonical morphism from the source to the base. -/
@[simp] theorem sourceToBase_toToposHom (π' : MorphismOfTopoi
      (Sheaf S.sourceTopology (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))
      (Sheaf S.base.J (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))) :
    (S.sourceToBase π').toToposHom = π' := rfl

/-- The structure map of the canonical morphism from the source to the base. -/
@[simp] theorem sourceToBase_fSharp (π' : MorphismOfTopoi
      (Sheaf S.sourceTopology (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))
      (Sheaf S.base.J (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))) :
    (S.sourceToBase π').fSharp = (commRingImageAdjunction π').unit.app S.base.O := rfl

/-- The structure map of the canonical morphism from the source to the base, with the base
structure sheaf spelled through the base *ringed topos*. This is the spelling in which
`Stacks.Sheaves.ToposPushforward.forgetRing_map_commRingImageAdjunction_unit_app` presents it, and
matching it on the nose is what lets that lemma be applied. -/
@[simp] theorem sourceToBase_fSharp_baseTopos
    (π' : MorphismOfTopoi
      (Sheaf S.sourceTopology (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))
      (Sheaf S.base.J (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))) :
    (S.sourceToBase π').fSharp =
      (commRingImageAdjunction π').unit.app S.baseTopos.O := rfl

/-! ### The identification `g⁻¹O_C = O_{C'}`

The three inverse images are restriction along `p`, `p'` and `u`, so each structure sheaf is the
restriction of `O_D` as a sheaf of *commutative rings*
(`Stacks.Sheaves.ToposPullback.restrictionCommRingIso`), and `p' = u ⋙ p` turns the iterated
restriction into the single one.
-/

/-- The structure sheaf of the target ringed topos is the restriction of `O_D` along `p`, as a
sheaf of commutative rings. -/
noncomputable def totalStructureRestrictionIso :
    (S.totalTopos S.pi).O ≅
      (S.p.sheafPushforwardContinuous CommRingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
        S.totalTopology S.base.J).obj S.base.O :=
  restrictionCommRingIso S.totalTopology S.base.J S.p S.base.O

/-- The structure sheaf of the source ringed topos is the restriction of `O_D` along `p'`, as a
sheaf of commutative rings. -/
noncomputable def sourceStructureRestrictionIso :
    (S.sourceTopos S.pi').O ≅
      (S.p'.sheafPushforwardContinuous CommRingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
        S.sourceTopology S.base.J).obj S.base.O :=
  restrictionCommRingIso S.sourceTopology S.base.J S.p' S.base.O

/-- The functor forgetting the ring operations of a sheaf of commutative rings on the source
site. Introduced so that the comparisons below mention it without re-resolving its
`GrothendieckTopology.HasSheafCompose` hypotheses at every occurrence. -/
noncomputable abbrev sourceForget :=
  sheafCompose S.sourceTopology (forget CommRingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})

/-- The functor forgetting the ring operations of a sheaf of commutative rings on the target
site. -/
noncomputable abbrev totalForget :=
  sheafCompose S.totalTopology (forget CommRingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})

/-- The functor forgetting the ring operations of a sheaf of commutative rings on the base
site. -/
noncomputable abbrev baseForget :=
  sheafCompose S.base.J (forget CommRingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})

/-- Restriction of sheaves of commutative rings along `u`. -/
noncomputable abbrev sourceRestrictCommRing :=
  S.u.sheafPushforwardContinuous CommRingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
    S.sourceTopology S.totalTopology

/-- The comparison of the two restrictions, on sheaves of sets, at the base structure sheaf. This
is the one factor of `structureComparison` that survives forgetting the ring operations. -/
noncomputable abbrev restrictionComp :=
  (CategoryTheory.Functor.sheafPushforwardContinuousComp'
    (eqToIso S.isFibredOneMorphism.comp_eq) (Type (max w u₀ u₁ u₂ v₀ v₁ v₂))
    S.sourceTopology S.totalTopology S.base.J).hom.app (S.baseForget.obj S.base.O)

/-- The functor forgetting the ring operations on the source ringed topos, as a functor equation.
Unlike the projection `sourceTopos_J`, this is safe to rewrite with: it replaces the whole functor
at once, so the goal stays type-correct at every transparency level. -/
@[simp] theorem sourceTopos_forgetRing
    (π' : MorphismOfTopoi
      (Sheaf S.sourceTopology (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))
      (Sheaf S.base.J (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))) :
    sheafCompose (S.sourceTopos π').J (forget CommRingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) =
      S.sourceForget := rfl

/-- Forgetting the ring operations of the structure sheaf of the source ringed topos gives the
inverse image of the underlying sheaf of sets of `O_D`. This is
`Stacks.Sheaves.ToposPullback.forget_pullbackCommRingSheaf` at the situation's data, stated on its
own so that the comparison below never has to rediscover it. -/
@[simp] theorem sourceForget_obj_sourceTopos_O
    (π' : MorphismOfTopoi
      (Sheaf S.sourceTopology (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))
      (Sheaf S.base.J (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))) :
    S.sourceForget.obj (S.sourceTopos π').O =
      π'.inverseImage.obj (S.baseForget.obj S.base.O) :=
  rfl

/-- **Stacks 08PA**, the observation `g⁻¹O_C = O_{C'}`. Both structure sheaves are inverse images
of `O_D`, the first through `π` and then `g`, the second through `π'`; since all three inverse
images are restriction and `p' = u ⋙ p`, the two agree.

The factors are ordered so that only the first mentions `g`: after it, every object is a
restriction of a sheaf of commutative rings, which is what keeps the comparison with the
set-valued statement cheap. -/
noncomputable def structureComparison :
    (inverseImageCommRingFunctor S.g).obj (S.totalTopos S.pi).O ≅ (S.sourceTopos S.pi').O :=
  restrictionCommRingIso S.sourceTopology S.totalTopology S.u (S.totalTopos S.pi).O ≪≫
    S.sourceRestrictCommRing.mapIso S.totalStructureRestrictionIso ≪≫
      (CategoryTheory.Functor.sheafPushforwardContinuousComp'
        (eqToIso S.isFibredOneMorphism.comp_eq) CommRingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
        S.sourceTopology S.totalTopology S.base.J).app S.base.O ≪≫
      S.sourceStructureRestrictionIso.symm

/-- The canonical morphism of ringed topoi `g : (Sh(C'), O_{C'}) ⟶ (Sh(C), O_C)`: its structure
map is the adjunct of the identification `g⁻¹O_C ≅ O_{C'}`. -/
noncomputable def gRinged :
    AlgebraicGeometry.RingedToposHom (S.sourceTopos S.pi') (S.totalTopos S.pi) where
  toToposHom := S.g
  fSharp := (commRingImageAdjunction S.g).homEquiv _ _ S.structureComparison.hom

/-- The underlying morphism of topoi of `gRinged` is `g`. -/
@[simp] theorem gRinged_toToposHom : S.gRinged.toToposHom = S.g := rfl

/-- The inverse-image form of the structure map of `gRinged` is the identification
`g⁻¹O_C ≅ O_{C'}`, hence an isomorphism. -/
theorem gRinged_fSharpInverseImage :
    S.gRinged.fSharpInverseImage = S.structureComparison.hom :=
  ((commRingImageAdjunction S.g).homEquiv _ _).symm_apply_apply _

/-- **Stacks 08PA, the observation `g⁻¹O_C = O_{C'}`, as an instance.** The structure map of `g`
in inverse-image form is the identification `structureComparison`, hence invertible. -/
instance isIso_gRinged_fSharpInverseImage : IsIso S.gRinged.fSharpInverseImage :=
  S.gRinged_fSharpInverseImage ▸ S.structureComparison.isIso_hom

/-- The canonical comparison of the inverse image along the composite `π ∘ g` with the inverse
image along `π'`, on sheaves of sets: restriction along `p` then along `u` is restriction along
`p' = u ⋙ p`. -/
noncomputable def inverseImageComparison :
    (S.pi.comp S.g).inverseImage ≅ S.pi'.inverseImage :=
  eqToIso (congrArg₂ (· ⋙ ·) (rfl : S.pi.inverseImage = S.p.sheafPushforwardContinuous
      (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)) S.totalTopology S.base.J)
    (rfl : S.g.inverseImage = S.u.sheafPushforwardContinuous
      (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)) S.sourceTopology S.totalTopology)) ≪≫
    CategoryTheory.Functor.sheafPushforwardContinuousComp'
      (eqToIso S.isFibredOneMorphism.comp_eq) (Type (max w u₀ u₁ u₂ v₀ v₁ v₂))
      S.sourceTopology S.totalTopology S.base.J ≪≫
    eqToIso (rfl : S.pi'.inverseImage = S.p'.sheafPushforwardContinuous
      (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)) S.sourceTopology S.base.J).symm

/-- The canonical comparison of inverse images is, in the one component that matters, exactly the
comparison of the two restrictions: the two `eqToIso` factors are identities. -/
theorem inverseImageComparison_hom_app :
    S.inverseImageComparison.hom.app (S.baseForget.obj S.base.O) = S.restrictionComp :=
  (Category.id_comp _).trans (Category.comp_id _)

/-- The inverse-image form of the structure map of the canonical morphism to the base is the
identity: that structure map is the unit of the adjunction, whose adjunct is the identity. -/
theorem toBase_fSharpInverseImage
    (π : MorphismOfTopoi
      (Sheaf S.totalTopology (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))
      (Sheaf S.base.J (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))) :
    (S.toBase π).fSharpInverseImage = 𝟙 ((inverseImageCommRingFunctor π).obj S.base.O) :=
  (congrArg ((commRingImageAdjunction π).homEquiv S.base.O
        ((inverseImageCommRingFunctor π).obj S.base.O)).symm
      (Adjunction.homEquiv_id (commRingImageAdjunction π) S.base.O).symm).trans
    (((commRingImageAdjunction π).homEquiv S.base.O
      ((inverseImageCommRingFunctor π).obj S.base.O)).symm_apply_apply _)

/-! ### Forgetting the ring operations of the identification `g⁻¹O_C ≅ O_{C'}` -/

/-- Restriction of sheaves of commutative rings along `u` commutes with forgetting the ring
operations, on the nose. -/
theorem forget_map_sourceRestrictCommRing_map
    {A B : Sheaf S.totalTopology CommRingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}} (h : A ⟶ B) :
    S.sourceForget.map (S.sourceRestrictCommRing.map h) =
      (S.u.sheafPushforwardContinuous (Type (max w u₀ u₁ u₂ v₀ v₁ v₂))
          S.sourceTopology S.totalTopology).map (S.totalForget.map h) :=
  rfl

/-- Forgetting the ring operations carries the `CommRingCat`-valued comparison of the two
restrictions to the `Type`-valued one: both are the action of `CategoryTheory.NatTrans.op` of the
comparison `u ⋙ p ≅ p'`, which commutes with post-composition by the forgetful functor. -/
theorem forget_map_restrictionCommRingComp :
    S.sourceForget.map
        ((CategoryTheory.Functor.sheafPushforwardContinuousComp'
          (eqToIso S.isFibredOneMorphism.comp_eq) CommRingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
          S.sourceTopology S.totalTopology S.base.J).app S.base.O).hom =
      S.restrictionComp :=
  rfl

/-- The comparison identifying `g⁻¹O_C` with its restriction along `u` is the identity on
underlying sheaves of sets. -/
theorem forget_map_restrictionCommRingIso_u :
    S.sourceForget.map
        (restrictionCommRingIso S.sourceTopology S.totalTopology S.u
          (S.totalTopos S.pi).O).hom =
      𝟙 (S.sourceForget.obj (S.sourceRestrictCommRing.obj (S.totalTopos S.pi).O)) :=
  restrictionCommRingIso_hom_forget S.sourceTopology S.totalTopology S.u (S.totalTopos S.pi).O

/-- A functor carries a morphism equal to an identity to an identity. -/
private theorem map_eq_id_of_eq_id {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {X : C}
    {f : X ⟶ X} (h : f = 𝟙 X) : F.map f = 𝟙 (F.obj X) :=
  h ▸ F.map_id X

/-- A functor carries a composite to the composite of any two given images of the factors. -/
private theorem map_comp_eq_of_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {a : F.obj X ⟶ F.obj Y} {b : F.obj Y ⟶ F.obj Z}
    (hf : F.map f = a) (hg : F.map g = b) : F.map (f ≫ g) = a ≫ b :=
  (F.map_comp f g).trans (congrArg₂ (· ≫ ·) hf hg)

/-- Restriction along `u` of the identification of `O_C` with the restriction of `O_D` along `p`
is the identity on underlying sheaves of sets. -/
theorem forget_map_sourceRestrict_totalStructureRestrictionIso :
    S.sourceForget.map (S.sourceRestrictCommRing.map S.totalStructureRestrictionIso.hom) =
      𝟙 _ :=
  (S.forget_map_sourceRestrictCommRing_map S.totalStructureRestrictionIso.hom).trans
    (map_eq_id_of_eq_id _
      (restrictionCommRingIso_hom_forget S.totalTopology S.base.J S.p S.base.O))

/-- The identification of `O_{C'}` with the restriction of `O_D` along `p'` is the identity on
underlying sheaves of sets, in the inverse direction. -/
theorem forget_map_sourceStructureRestrictionIso_inv :
    S.sourceForget.map S.sourceStructureRestrictionIso.inv = 𝟙 _ :=
  restrictionCommRingIso_inv_forget S.sourceTopology S.base.J S.p' S.base.O

/-- The identification `g⁻¹O_C ≅ O_{C'}` written out as a composite of its four factors. -/
theorem structureComparison_hom :
    S.structureComparison.hom =
      (restrictionCommRingIso S.sourceTopology S.totalTopology S.u
          (S.totalTopos S.pi).O).hom ≫
        (S.sourceRestrictCommRing.map S.totalStructureRestrictionIso.hom ≫
          (((CategoryTheory.Functor.sheafPushforwardContinuousComp'
                (eqToIso S.isFibredOneMorphism.comp_eq) CommRingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
                S.sourceTopology S.totalTopology S.base.J).app S.base.O).hom ≫
            S.sourceStructureRestrictionIso.inv)) :=
  rfl

/-- The last two factors of `structureComparison`, after forgetting the ring operations. -/
theorem forget_map_structureComparison_tail :
    S.sourceForget.map
        (((CategoryTheory.Functor.sheafPushforwardContinuousComp'
              (eqToIso S.isFibredOneMorphism.comp_eq) CommRingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
              S.sourceTopology S.totalTopology S.base.J).app S.base.O).hom ≫
          S.sourceStructureRestrictionIso.inv) =
      S.restrictionComp :=
  (map_comp_eq_of_eq _ S.forget_map_restrictionCommRingComp
    S.forget_map_sourceStructureRestrictionIso_inv).trans (Category.comp_id _)

/-- The last three factors of `structureComparison`, after forgetting the ring operations. -/
theorem forget_map_structureComparison_tail' :
    S.sourceForget.map
        (S.sourceRestrictCommRing.map S.totalStructureRestrictionIso.hom ≫
          (((CategoryTheory.Functor.sheafPushforwardContinuousComp'
                (eqToIso S.isFibredOneMorphism.comp_eq) CommRingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
                S.sourceTopology S.totalTopology S.base.J).app S.base.O).hom ≫
            S.sourceStructureRestrictionIso.inv)) =
      S.restrictionComp :=
  (map_comp_eq_of_eq _ S.forget_map_sourceRestrict_totalStructureRestrictionIso
    S.forget_map_structureComparison_tail).trans (Category.id_comp _)

/-- The first factor of `structureComparison` split off, after forgetting the ring operations. -/
theorem forget_map_structureComparison_split :
    S.sourceForget.map S.structureComparison.hom =
      S.sourceForget.map (restrictionCommRingIso S.sourceTopology S.totalTopology S.u
          (S.totalTopos S.pi).O).hom ≫
        S.sourceForget.map
          (S.sourceRestrictCommRing.map S.totalStructureRestrictionIso.hom ≫
            (((CategoryTheory.Functor.sheafPushforwardContinuousComp'
                  (eqToIso S.isFibredOneMorphism.comp_eq) CommRingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
                  S.sourceTopology S.totalTopology S.base.J).app S.base.O).hom ≫
              S.sourceStructureRestrictionIso.inv)) :=
  (congrArg S.sourceForget.map S.structureComparison_hom).trans
    (S.sourceForget.map_comp _ _)

/-- Forgetting the ring operations carries the identification `g⁻¹O_C ≅ O_{C'}` to the comparison
of the two restrictions on sheaves of sets: each of its other three factors is the identity
there. -/
theorem forget_map_structureComparison :
    S.sourceForget.map S.structureComparison.hom = S.restrictionComp :=
  (congrArg S.sourceForget.map S.structureComparison_hom).trans
    ((map_comp_eq_of_eq _ S.forget_map_restrictionCommRingIso_u
      S.forget_map_structureComparison_tail').trans (Category.id_comp _))

/-! ### The commutativity of the triangle -/

/-- The canonical 2-isomorphism `π_* ∘ g_* ≅ (π')_*`, the adjoint mate of the comparison of
inverse images. -/
noncomputable def commutativityIso :
    (S.pi.comp S.g).pushforward ≅ S.pi'.pushforward :=
  eqToIso (congrArg MorphismOfTopoi.pushforward
      (congrArg (MorphismOfTopoi.comp S.pi) (rfl : S.gRinged.toToposHom = S.g))) ≪≫
    ((S.pi.comp S.g).adj.ofNatIsoLeft S.inverseImageComparison).rightAdjointUniq S.pi'.adj

/-- The unit of the adjunction of `π'` twisted along the comparison of inverse images, written
out. -/
theorem ofNatIsoLeft_unit_app :
    ((S.pi.comp S.g).adj.ofNatIsoLeft S.inverseImageComparison).unit.app
        (S.baseForget.obj S.base.O) =
      (S.pi.comp S.g).adj.unit.app (S.baseForget.obj S.base.O) ≫
        (S.pi.comp S.g).pushforward.map
          (S.inverseImageComparison.hom.app (S.baseForget.obj S.base.O)) :=
  rfl

/-- The defining property of the mate, as an instance of
`CategoryTheory.Adjunction.unit_rightAdjointUniq_hom_app`. -/
theorem unit_comp_mate :
    ((S.pi.comp S.g).adj.ofNatIsoLeft S.inverseImageComparison).unit.app
        (S.baseForget.obj S.base.O) ≫
      (((S.pi.comp S.g).adj.ofNatIsoLeft S.inverseImageComparison).rightAdjointUniq
          S.pi'.adj).hom.app (S.pi'.inverseImage.obj (S.baseForget.obj S.base.O)) =
      S.pi'.adj.unit.app (S.baseForget.obj S.base.O) :=
  Adjunction.unit_rightAdjointUniq_hom_app _ _ _

/-- The unit of the twisted adjunction, written with the comparison of the two restrictions. -/
theorem unit_ofNatIsoLeft_eq :
    (S.pi.comp S.g).adj.unit.app (S.baseForget.obj S.base.O) ≫
        (S.pi.comp S.g).pushforward.map S.restrictionComp =
      ((S.pi.comp S.g).adj.ofNatIsoLeft S.inverseImageComparison).unit.app
        (S.baseForget.obj S.base.O) :=
  (congrArg (fun m ↦ (S.pi.comp S.g).adj.unit.app (S.baseForget.obj S.base.O) ≫
      (S.pi.comp S.g).pushforward.map m) S.inverseImageComparison_hom_app.symm).trans
    S.ofNatIsoLeft_unit_app.symm

/-- The defining property of the mate, with the comparison of the two restrictions in place of the
comparison of inverse images. -/
theorem unit_comp_mate' :
    ((S.pi.comp S.g).adj.unit.app (S.baseForget.obj S.base.O) ≫
        (S.pi.comp S.g).pushforward.map S.restrictionComp) ≫
      (((S.pi.comp S.g).adj.ofNatIsoLeft S.inverseImageComparison).rightAdjointUniq
          S.pi'.adj).hom.app (S.pi'.inverseImage.obj (S.baseForget.obj S.base.O)) =
      S.pi'.adj.unit.app (S.baseForget.obj S.base.O) :=
  by rw [S.unit_ofNatIsoLeft_eq]; exact S.unit_comp_mate

/-- The inverse image along `g` of the structure map of `π` is the identity on underlying sheaves
of sets: that structure map is itself an identity. -/
theorem forget_map_inverseImage_toBase_fSharpInverseImage :
    S.gRinged.toToposHom.inverseImage.map
        (S.totalForget.map (S.toBase S.pi).fSharpInverseImage) = 𝟙 _ :=
  map_eq_id_of_eq_id _ (map_eq_id_of_eq_id _ (S.toBase_fSharpInverseImage S.pi))

/-- The structure map of `g` in inverse-image form, after forgetting the ring operations. -/
theorem forget_map_gRinged_fSharpInverseImage :
    S.sourceForget.map S.gRinged.fSharpInverseImage = S.restrictionComp :=
  (congrArg S.sourceForget.map S.gRinged_fSharpInverseImage).trans
    S.forget_map_structureComparison

/-- The 2-isomorphism of the triangle is the mate: its `eqToIso` factor is the identity. -/
theorem commutativityIso_hom_app (Z : Sheaf S.sourceTopology (Type (max w u₀ u₁ u₂ v₀ v₁ v₂))) :
    S.commutativityIso.hom.app Z =
      (((S.pi.comp S.g).adj.ofNatIsoLeft S.inverseImageComparison).rightAdjointUniq
        S.pi'.adj).hom.app Z :=
  Category.id_comp _

/-- `unit_comp_mate'` with the forgetful functor written out rather than through the
abbreviation `baseForget`. That is the spelling the `commutes` field of `RingedToposDiagram`
presents, and `rw` matches on the nose only. -/
theorem unit_comp_mate_spelled :
    ((S.pi.comp S.g).adj.unit.app
          ((sheafCompose S.base.J (forget CommRingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})).obj S.base.O) ≫
        (S.pi.comp S.g).pushforward.map S.restrictionComp) ≫
      (((S.pi.comp S.g).adj.ofNatIsoLeft S.inverseImageComparison).rightAdjointUniq
          S.pi'.adj).hom.app
          (S.pi'.inverseImage.obj (S.baseForget.obj S.base.O)) =
      S.pi'.adj.unit.app
        ((sheafCompose S.base.J (forget CommRingCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})).obj S.base.O) :=
  S.unit_comp_mate'

/-- `unit_comp_mate'` with the base structure sheaf and its forgetful functor spelled through the
base *ringed topos*, which is the spelling the `commutes` field of `RingedToposDiagram`
presents. -/
theorem unit_comp_mate_baseTopos :
    ((S.pi.comp S.g).adj.unit.app (S.baseTopos.forgetRing.obj S.baseTopos.O) ≫
        (S.pi.comp S.g).pushforward.map S.restrictionComp) ≫
      (((S.pi.comp S.g).adj.ofNatIsoLeft S.inverseImageComparison).rightAdjointUniq
          S.pi'.adj).hom.app (S.pi'.inverseImage.obj (S.baseForget.obj S.base.O)) =
      S.pi'.adj.unit.app (S.baseTopos.forgetRing.obj S.baseTopos.O) :=
  S.unit_comp_mate'

/-! ### The diagram -/

/-- **Stacks 08PA.** The induced geometric maps and the commutative diagram of ringed topoi. The
equalities identify each geometric inverse image with restriction along the corresponding functor
and each direct image with its right Kan extension, so that the maps the source names are pinned
rather than merely asserted to exist. -/
structure RingedToposDiagram where
  /-- `p` is a continuous functor for the inherited topologies. -/
  pContinuous : S.p.IsContinuous S.totalTopology S.base.J
  /-- `p` is a cocontinuous functor for the inherited topologies. -/
  pCocontinuous : S.p.IsCocontinuous S.totalTopology S.base.J
  /-- `p'` is a continuous functor for the inherited topologies. -/
  p'Continuous : S.p'.IsContinuous S.sourceTopology S.base.J
  /-- `p'` is a cocontinuous functor for the inherited topologies. -/
  p'Cocontinuous : S.p'.IsCocontinuous S.sourceTopology S.base.J
  /-- `u` is a continuous functor for the two inherited topologies. -/
  uContinuous : S.u.IsContinuous S.sourceTopology S.totalTopology
  /-- `u` is a cocontinuous functor for the two inherited topologies. -/
  uCocontinuous : S.u.IsCocontinuous S.sourceTopology S.totalTopology
  /-- The morphism of topoi `π : Sh(C) ⟶ Sh(D)`. -/
  pi : MorphismOfTopoi (Sheaf S.totalTopology (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))
    (Sheaf S.base.J (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))
  /-- The morphism of topoi `π' : Sh(C') ⟶ Sh(D)`. -/
  pi' : MorphismOfTopoi (Sheaf S.sourceTopology (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))
    (Sheaf S.base.J (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))
  /-- The morphism of topoi `g : Sh(C') ⟶ Sh(C)`. -/
  g : MorphismOfTopoi (Sheaf S.sourceTopology (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))
    (Sheaf S.totalTopology (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))
  /-- The inverse image of `π` is restriction along `p`. -/
  pi_inverseImage :
    letI := pContinuous
    pi.inverseImage = S.p.sheafPushforwardContinuous
      (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)) S.totalTopology S.base.J
  /-- The direct image of `π` is the right Kan extension along `p`. -/
  pi_pushforward :
    letI := pCocontinuous
    pi.pushforward = S.p.sheafPushforwardCocontinuous
      (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)) S.totalTopology S.base.J
  /-- The inverse image of `π'` is restriction along `p'`. -/
  pi'_inverseImage :
    letI := p'Continuous
    pi'.inverseImage = S.p'.sheafPushforwardContinuous
      (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)) S.sourceTopology S.base.J
  /-- The direct image of `π'` is the right Kan extension along `p'`. -/
  pi'_pushforward :
    letI := p'Cocontinuous
    pi'.pushforward = S.p'.sheafPushforwardCocontinuous
      (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)) S.sourceTopology S.base.J
  /-- The inverse image of `g` is restriction along `u`. -/
  g_inverseImage :
    letI := uContinuous
    g.inverseImage = S.u.sheafPushforwardContinuous
      (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)) S.sourceTopology S.totalTopology
  /-- The direct image of `g` is the right Kan extension along `u`. -/
  g_pushforward :
    letI := uCocontinuous
    g.pushforward = S.u.sheafPushforwardCocontinuous
      (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)) S.sourceTopology S.totalTopology
  /-- `g` as a morphism of ringed topoi. -/
  gRinged : AlgebraicGeometry.RingedToposHom (S.sourceTopos pi') (S.totalTopos pi)
  /-- Its underlying morphism of topoi is `g`. -/
  g_underlying : gRinged.toToposHom = g
  /-- The inverse-image structure map is an isomorphism, as both structure sheaves are pulled back
  from the same sheaf on the base. -/
  gRinged_fSharpInverseImage_isIso : IsIso gRinged.fSharpInverseImage
  /-- The comparison on inverse images, before taking its adjoint mate. -/
  inverseImageComparison : (pi.comp g).inverseImage ≅ pi'.inverseImage
  /-- Restriction along `p' = u ⋙ p` is the specific comparison used here. -/
  inverseImageComparison_canonical :
    letI := pContinuous
    letI := uContinuous
    letI := p'Continuous
    inverseImageComparison =
      eqToIso (congrArg₂ (· ⋙ ·) pi_inverseImage g_inverseImage) ≪≫
        CategoryTheory.Functor.sheafPushforwardContinuousComp'
          (eqToIso S.isFibredOneMorphism.comp_eq)
          (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)) S.sourceTopology S.totalTopology S.base.J ≪≫
        eqToIso pi'_inverseImage.symm
  /-- The two geometric composites agree up to the canonical 2-isomorphism. -/
  commutativityIso :
    ((S.toBase pi).toToposHom.comp gRinged.toToposHom).pushforward ≅
      (S.sourceToBase pi').toToposHom.pushforward
  /-- The direct-image comparison is the adjoint mate of the inverse-image comparison, rather than
  an independently chosen automorphism. -/
  commutativityIso_isMate :
    commutativityIso =
      eqToIso (congrArg MorphismOfTopoi.pushforward
        (congrArg (MorphismOfTopoi.comp pi) g_underlying)) ≪≫
          ((pi.comp g).adj.ofNatIsoLeft inverseImageComparison).rightAdjointUniq pi'.adj
  /-- The 2-isomorphism respects the structure maps after forgetting the ring operations. -/
  commutes :
    S.baseTopos.forgetRing.map
          (AlgebraicGeometry.RingedToposHom.compFSharp (S.toBase pi) gRinged) ≫
        (pushforwardCommRingForgetIso (J := (S.sourceTopos pi').J) (K := S.baseTopos.J)
            (f := (S.toBase pi).toToposHom.comp gRinged.toToposHom)).hom.app
            (S.sourceTopos pi').O ≫
          commutativityIso.hom.app
            ((S.sourceTopos pi').forgetRing.obj (S.sourceTopos pi').O) =
      S.baseTopos.forgetRing.map (S.sourceToBase pi').fSharp ≫
        (pushforwardCommRingForgetIso (J := (S.sourceTopos pi').J) (K := S.baseTopos.J)
          (f := (S.sourceToBase pi').toToposHom)).hom.app (S.sourceTopos pi').O

end Diagram

end MorphismSituation

end Stacks.Sites.FibredCategory

end
