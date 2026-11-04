module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RelativeCupProduct
import StacksCore.Tactic.StacksAttribute

/-!
# The naive relative cup product in degree zero against a coherator

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi.  The *naive relative cup
product in degree zero* is the map

`c : f_*F ⊗_{O_D} f_*G ⟶ f_*(F ⊗_{O_C} G)`

of Tag 0FPJ: the map adjoint, for the adjunction `f^* ⊣ f_*` of Tag 03D7, to the comparison
`f^*(f_*F ⊗ f_*G) ≅ f^*f_*F ⊗ f^*f_*G` of Tag 03EL followed by the counit `f^*f_* ⟶ id` in each
tensor factor.

Let moreover `i ⊣ Q` be an adjunction into `Mod(O_D)`, with `i` carrying a tensor product on its
source to the tensor product of `Mod(O_D)`.  Then there is a canonical map

`Q(f_*F) ⊗ Q(f_*G) ⟶ Q(f_*(F ⊗_{O_C} G))`,

and the square whose horizontal arrows are the counit of `i ⊣ Q` and whose vertical arrows are
that map and `c` commutes.  This is Tag 0GQR with `Q` the coherator and `i` the inclusion of the
quasi-coherent modules.

## Main definitions

* `Stacks.Cohomology.DegreeZeroCupProduct.coheratorCupProduct` — the image of a map out of a
  tensor product under the comparison attached to an adjunction, in the abstract setting.
* `Stacks.Cohomology.DegreeZeroCupProduct.naiveRelativeCupProduct` — the map `c`.
* `Stacks.Cohomology.DegreeZeroCupProduct.quasicoherentRelativeCupProduct` — the comparison of
  the adjunction at the naive relative cup product in degree zero.

## Main results

* `Stacks.Cohomology.DegreeZeroCupProduct.map_coheratorCupProduct_comp_counit` and
  `Stacks.Cohomology.DegreeZeroCupProduct.map_quasicoherentRelativeCupProduct_comp_counit` — the
  commutativity of the square, abstractly and at the naive relative cup product.
* `Stacks.Cohomology.DegreeZeroCupProduct.coheratorCupProduct_natural`,
  `Stacks.Cohomology.DegreeZeroCupProduct.naiveRelativeCupProduct_natural` and
  `Stacks.Cohomology.DegreeZeroCupProduct.quasicoherentRelativeCupProduct_natural` —
  functoriality of each construction in the two modules.

## Implementation notes

The adjunction `i ⊣ Q`, the tensor product `A` on the source of `i` and the comparison `α`
carrying `A` to the tensor product of `Mod(O_D)` are taken as data: for Tag 0GQR they are the
inclusion of the quasi-coherent modules, the coherator of Tag 0778 and the compatibility of the
coherator with tensor products of Tag 0GQM, none of which is constructed here. The square
commutes for every adjunction with a tensor comparison. Both statements are made for a morphism of
ringed topoi and arbitrary modules `F`, `G`; the identification of `Q(f_*(-))` with the functor
`f_{QCoh, *}` of Tag 077A is not asserted. The `example` at the end of the file instantiates the
data at the pullback-pushforward adjunction of a second morphism of ringed topoi, with `α` the
comparison of Tag 03EL.

## References

* [Stacks Project, Tag 0GQR](https://stacks.math.columbia.edu/tag/0GQR)
* [Stacks Project, Tag 0FPJ](https://stacks.math.columbia.edu/tag/0FPJ)
* [Stacks Project, Tag 0GQM](https://stacks.math.columbia.edu/tag/0GQM)
* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.SheafOfModules.Tensor (sheafTensor)
open AlgebraicGeometry.SheafOfModules
open Stacks.Cohomology.RelativeCupProductOnRingedTopoi
open Stacks.Sheaves.RingedToposModules
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.DegreeZeroCupProduct

/-! ### The comparison attached to an adjunction -/

section Abstract

variable {𝒬 : Type*} {𝒞 : Type*} [Category 𝒬] [Category 𝒞]
  {i : 𝒬 ⥤ 𝒞} {Q : 𝒞 ⥤ 𝒬} (adj : i ⊣ Q)
  (A : 𝒬 × 𝒬 ⥤ 𝒬) (B : 𝒞 × 𝒞 ⥤ 𝒞) (α : A ⋙ i ⟶ i.prod i ⋙ B)

/-- The image under the comparison of `adj : i ⊣ Q` of a map `c : B(M, N) ⟶ P` out of a tensor
product: the canonical map `A(Q M, Q N) ⟶ Q(B(M, N))` followed by `Q c`. -/
def coheratorCupProduct {M N P : 𝒞} (c : B.obj (M, N) ⟶ P) :
    A.obj (Q.obj M, Q.obj N) ⟶ Q.obj P :=
  adjunctionCupProduct adj A B α M N ≫ Q.map c

/-- **The square commutes.**  The comparison `α`, followed by the counit of `adj` in each tensor
factor and then by `c`, equals `i` of
`Stacks.Cohomology.DegreeZeroCupProduct.coheratorCupProduct` followed by the counit of `adj`. -/
theorem map_coheratorCupProduct_comp_counit {M N P : 𝒞} (c : B.obj (M, N) ⟶ P) :
    i.map (coheratorCupProduct adj A B α c) ≫ adj.counit.app P =
      α.app (Q.obj M, Q.obj N) ≫ B.map (adj.counit.app M ×ₘ adj.counit.app N) ≫ c := by
  have h : (adj.homEquiv (A.obj (Q.obj M, Q.obj N)) (B.obj (M, N))).symm
        (adjunctionCupProduct adj A B α M N) =
      α.app (Q.obj M, Q.obj N) ≫ B.map (adj.counit.app M ×ₘ adj.counit.app N) :=
    (adj.homEquiv _ _).symm_apply_apply _
  rw [Adjunction.homEquiv_counit] at h
  unfold coheratorCupProduct
  rw [Functor.map_comp, Category.assoc, adj.counit_naturality c, ← Category.assoc, h,
    Category.assoc]

/-- **The construction is functorial in the two objects.**  A pair of maps `g`, `k` compatible
with `c` and `c'` through `p` is carried to the corresponding square for
`Stacks.Cohomology.DegreeZeroCupProduct.coheratorCupProduct`. -/
theorem coheratorCupProduct_natural {M M' N N' P P' : 𝒞} (g : M ⟶ M') (k : N ⟶ N')
    (c : B.obj (M, N) ⟶ P) (c' : B.obj (M', N') ⟶ P') (p : P ⟶ P')
    (hc : B.map (g ×ₘ k) ≫ c' = c ≫ p) :
    A.map (Q.map g ×ₘ Q.map k) ≫ coheratorCupProduct adj A B α c' =
      coheratorCupProduct adj A B α c ≫ Q.map p := by
  unfold coheratorCupProduct
  rw [← Category.assoc, adjunctionCupProduct_natural adj A B α g k, Category.assoc,
    ← Q.map_comp, hc, Q.map_comp, Category.assoc]

end Abstract

/-! ### The naive relative cup product in degree zero -/

universe w w' v u v' u'

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)

/-- **The naive relative cup product in degree zero**, the map
`f_*F ⊗_{O_D} f_*G ⟶ f_*(F ⊗_{O_C} G)` adjoint to the comparison of Tag 03EL followed by the
counit of `f^* ⊣ f_*` in each tensor factor. -/
@[stacks 0GQR "the vertical arrow c on the right, for a morphism of ringed topoi"]
def naiveRelativeCupProduct
    (F G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (Functor.uncurry.obj (sheafTensor.{u', v', w', w', w'} Y.O)).obj
          ((pushforwardModules f).obj F, (pushforwardModules f).obj G) ⟶
      (pushforwardModules f).obj
        ((Functor.uncurry.obj (sheafTensor.{u, v, w, w, w} X.O)).obj (F, G)) :=
  adjunctionCupProduct (pullbackAdjPushforwardModules f)
    (Functor.uncurry.obj (sheafTensor.{u', v', w', w', w'} Y.O))
    (Functor.uncurry.obj (sheafTensor.{u, v, w, w, w} X.O))
    (Stacks.SheafOfModules.pullbackTensorIso f).hom F G

/-- The naive relative cup product in degree zero is natural in the two modules jointly. -/
theorem naiveRelativeCupProduct_natural
    {F F' G G' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (u : F ⟶ F') (v : G ⟶ G') :
    (Functor.uncurry.obj (sheafTensor.{u', v', w', w', w'} Y.O)).map
          ((pushforwardModules f).map u ×ₘ (pushforwardModules f).map v) ≫
        naiveRelativeCupProduct f F' G' =
      naiveRelativeCupProduct f F G ≫
        (pushforwardModules f).map
          ((Functor.uncurry.obj (sheafTensor.{u, v, w, w, w} X.O)).map (u ×ₘ v)) :=
  adjunctionCupProduct_natural (pullbackAdjPushforwardModules f)
    (Functor.uncurry.obj (sheafTensor.{u', v', w', w', w'} Y.O))
    (Functor.uncurry.obj (sheafTensor.{u, v, w, w, w} X.O))
    (Stacks.SheafOfModules.pullbackTensorIso f).hom u v

/-! ### The diagram of Tag 0GQR -/

section Coherator

variable {𝒬 : Type*} [Category 𝒬]
  {i : 𝒬 ⥤ SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
  {Q : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤ 𝒬} (adj : i ⊣ Q)
  (A : 𝒬 × 𝒬 ⥤ 𝒬)
  (α : A ⋙ i ⟶ i.prod i ⋙ Functor.uncurry.obj (sheafTensor.{u', v', w', w', w'} Y.O))

/-- The naive relative cup product in degree zero carried through the comparison attached to the
adjunction `adj : i ⊣ Q` and the tensor comparison `α`: the canonical map
`A(Q(f_*F), Q(f_*G)) ⟶ Q(f_*F ⊗ f_*G)` followed by `Q` applied to `c`. -/
@[stacks 0GQR "the left vertical arrow, over an adjunction with a tensor comparison"]
def quasicoherentRelativeCupProduct
    (F G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    A.obj (Q.obj ((pushforwardModules f).obj F), Q.obj ((pushforwardModules f).obj G)) ⟶
      Q.obj ((pushforwardModules f).obj
        ((Functor.uncurry.obj (sheafTensor.{u, v, w, w, w} X.O)).obj (F, G))) :=
  coheratorCupProduct adj A (Functor.uncurry.obj (sheafTensor.{u', v', w', w', w'} Y.O)) α
    (naiveRelativeCupProduct f F G)

/-- **The square commutes.**  Going right along the upper horizontal
arrow — the comparison `α` followed by the counit of `adj` in each tensor factor — and then down
`c` agrees with going down the left vertical arrow and then right along the counit of `adj`. -/
@[stacks 0GQR "commutativity of the diagram, over an adjunction with a tensor comparison"]
theorem map_quasicoherentRelativeCupProduct_comp_counit
    (F G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    i.map (quasicoherentRelativeCupProduct f adj A α F G) ≫
        adj.counit.app ((pushforwardModules f).obj
          (((sheafTensor.{u, v, w, w, w} X.O).obj F).obj G)) =
      α.app (Q.obj ((pushforwardModules f).obj F), Q.obj ((pushforwardModules f).obj G)) ≫
        (Functor.uncurry.obj (sheafTensor.{u', v', w', w', w'} Y.O)).map
            (adj.counit.app ((pushforwardModules f).obj F) ×ₘ
              adj.counit.app ((pushforwardModules f).obj G)) ≫
          naiveRelativeCupProduct f F G :=
  map_coheratorCupProduct_comp_counit adj A
    (Functor.uncurry.obj (sheafTensor.{u', v', w', w', w'} Y.O)) α _

/-- **The construction is functorial in the two modules.** -/
@[stacks 0GQR "functoriality in the two modules, over an adjunction with a tensor comparison"]
theorem quasicoherentRelativeCupProduct_natural
    {F F' G G' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (u : F ⟶ F') (v : G ⟶ G') :
    A.map (Q.map ((pushforwardModules f).map u) ×ₘ Q.map ((pushforwardModules f).map v)) ≫
        quasicoherentRelativeCupProduct f adj A α F' G' =
      quasicoherentRelativeCupProduct f adj A α F G ≫
        Q.map ((pushforwardModules f).map
          ((Functor.uncurry.obj (sheafTensor.{u, v, w, w, w} X.O)).map (u ×ₘ v))) :=
  coheratorCupProduct_natural adj A
    (Functor.uncurry.obj (sheafTensor.{u', v', w', w', w'} Y.O)) α _ _ _ _ _
    (naiveRelativeCupProduct_natural f u v)

end Coherator

/-- The data carried in place of the coherator is realized by the pullback-pushforward
adjunction of a second morphism of ringed topoi together with the comparison of Tag 03EL, for
which neither of the two functors is an equivalence. -/
example {Z : RingedTopos.{v', u', w'}}
    [Z.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
    [Z.J.HasSheafCompose (forget RingCat.{w'})] [Z.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
    [HasWeakSheafify Z.J AddCommGrpCat.{w'}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    (g : Stacks.Sheaves.RingedToposModules.RingedToposHom Y Z)
    (F G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    ((sheafTensor.{u', v', w', w', w'} Z.O).obj
        ((pushforwardModules g).obj ((pushforwardModules f).obj F))).obj
        ((pushforwardModules g).obj ((pushforwardModules f).obj G)) ⟶
      (pushforwardModules g).obj ((pushforwardModules f).obj
        (((sheafTensor.{u, v, w, w, w} X.O).obj F).obj G)) :=
  quasicoherentRelativeCupProduct f (pullbackAdjPushforwardModules g)
    (Functor.uncurry.obj (sheafTensor.{u', v', w', w', w'} Z.O))
    (Stacks.SheafOfModules.pullbackTensorIso g).hom F G

end Stacks.Cohomology.DegreeZeroCupProduct

end
