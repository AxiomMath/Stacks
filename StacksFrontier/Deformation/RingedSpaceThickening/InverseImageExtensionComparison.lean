module

public import StacksFrontier.CategoryTheory.Sites.Modules.SquareZeroExtensionOverBase
import StacksCore.Tactic.StacksAttribute

/-!
# The pushout and pullback extensions of Stacks 0GQ2, and the criterion comparing them

Let `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` and `g : (Y, 𝒪_Y) ⟶ (X, 𝒪_X)` be morphisms of ringed spaces, let
`ℱ` be an `𝒪_X`-module, `𝒢` an `𝒪_Y`-module and `c : ℱ ⟶ 𝒢` a `g`-map, and let

* `0 ⟶ ℱ ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0` be an extension of `f^{-1}𝒪_S`-algebras, and
* `0 ⟶ 𝒢 ⟶ 𝒪_{Y'} ⟶ 𝒪_Y ⟶ 0` an extension of `g^{-1}f^{-1}𝒪_S`-algebras,

as in **Stacks 0GQ1**.  The remark **Stacks 0GQ2** builds from these two extensions of
`g^{-1}𝒪_X` by `𝒢` over `g^{-1}f^{-1}𝒪_S` —

* `𝒪'₁`, the pushout of `g^{-1}𝒪_{X'}` along `c : g^{-1}ℱ ⟶ 𝒢`, and
* `𝒪'₂ = 𝒪_{Y'} ×_{𝒪_Y} g^{-1}𝒪_X`, the pullback of `𝒪_{Y'}` along `g^♯` —

and proves that an `S`-morphism `Y' → X'` compatible with `g` and `c` exists if and only if
`𝒪'₁` and `𝒪'₂` are isomorphic as such extensions.  This file carries out both constructions
and proves that criterion.

Everything in sight lives on `Y`, so the whole content is about sheaves of commutative rings on
one site: `Stacks.Deformation.InverseImageExtension.Data` is the dictionary, with `A'` for
`g^{-1}𝒪_{X'}`, `A` for `g^{-1}𝒪_X`, `B'` for `𝒪_{Y'}`, `B` for `𝒪_Y` and `S` for
`g^{-1}f^{-1}𝒪_S`.  That `g^{-1}𝒪_{X'}` *is* an extension of `g^{-1}𝒪_X` by `g^{-1}ℱ` — that the
inverse image functor carries the short exact sequence of (a) to one — is assumed, not proved: the
square-zero ideal of `g^{-1}𝒪_{X'}` is taken to be the kernel ideal `Ker π` of the given locally
surjective `π : A' ⟶ A`, which is `g^{-1}ℱ`, and the map `c` is the
`Stacks.Sites.SqZeroPushout.PushoutData` the pushout consumes.

## Main definitions

* `Stacks.Deformation.InverseImageExtension.Data`: the setup of **Stacks 0GQ1** read on `Y`.
* `Stacks.Deformation.InverseImageExtension.Data.pushoutExtension`: the extension `𝒪'₁`.
* `Stacks.Deformation.InverseImageExtension.Data.pullbackExtension`: the extension `𝒪'₂`.
* `Stacks.Deformation.InverseImageExtension.Data.CompatibleHom`: an `S`-morphism `Y' → X'`
  compatible with `g` and `c`, read as a morphism `g^{-1}𝒪_{X'} ⟶ 𝒪_{Y'}` of
  `g^{-1}f^{-1}𝒪_S`-algebras over `g^♯` restricting to `c` on `g^{-1}ℱ`.
* `Stacks.Deformation.InverseImageExtension.Data.comparisonHom`: the comparison
  `𝒪'₁ ⟶ 𝒪'₂` built from such a morphism.

## Main results

* `Stacks.Deformation.InverseImageExtension.Data.pushoutMap_app_kernel`: the map
  `g^{-1}𝒪_{X'} ⟶ 𝒪'₁` carries `g^{-1}ℱ` to `𝒢` by `c`.
* `Stacks.Deformation.InverseImageExtension.Data.nonempty_compatibleHom_iff_isomorphic`:
  **the criterion of Stacks 0GQ2** — a compatible `S`-morphism exists if and only if `𝒪'₁` and
  `𝒪'₂` are isomorphic as extensions of `g^{-1}𝒪_X` by `𝒢` over `g^{-1}f^{-1}𝒪_S`.

## Implementation notes

The two constructions are `Stacks.Sites.SqZeroPushout.pushoutSheaf` and
`Stacks.Sites.SqZeroPullback.fibreSheaf`.  What this file adds is the packaging of each as a
`Stacks.Sites.SqZeroExtension.AlgebraExtension` — which for the pushout needs the relation
`Data.pushoutMap_app_kernel`, the only place the graph ideal is used directly — and the comparison
between them.

Two structural facts about `𝒢` are hypotheses rather than consequences, because the formalized
input is the surjection `p : 𝒪_{Y'} ⟶ 𝒪_Y` with a realization `ι` of its kernel and not a
ringed-space thickening: `Data.inr_mul_inr`, that the ideal of `𝒪_{Y'}` squares to zero, and
`Data.smul_inr`, that the `g^{-1}𝒪_{X'}`-module structure of `𝒢` is the restriction, along
`g^♯ ∘ π`, of the action of `𝒪_{Y'}` on its ideal.  Both are part of the source's standing
assumption that `𝒢` is an `𝒪_Y`-module which is the square-zero ideal of `𝒪_{Y'}`.

The criterion is proved in both directions and neither is assumed.  From a compatible morphism
`h` the comparison `𝒪'₁ ⟶ 𝒪'₂` is `(a, n) ↦ (h a + ι n, π a)`, descended through the graph
ideal and the sheafification; it is an isomorphism by
`Stacks.Sites.SqZeroExtension.AlgebraExtension.Hom.isIso`, the five lemma, so no inverse has to
be produced.  Conversely a morphism of extensions gives `h` by composing `g^{-1}𝒪_{X'} ⟶ 𝒪'₁`
with it and with the projection `𝒪'₂ ⟶ 𝒪_{Y'}`.

## References

* [Stacks Project, Tag 0GQ2](https://stacks.math.columbia.edu/tag/0GQ2)
* [Stacks Project, Tag 0GQ1](https://stacks.math.columbia.edu/tag/0GQ1)
* [Stacks Project, Tag 0GPW](https://stacks.math.columbia.edu/tag/0GPW)
* [Stacks Project, Tag 08UC](https://stacks.math.columbia.edu/tag/08UC)
-/

@[expose] public noncomputable section

open CategoryTheory PresheafOfModules Opposite
open Stacks.Sheaves.Differentials (underlyingRingSheaf sqZeroExtSheaf sqZeroExtSheafProj
  sqZeroExtSheafInl)
open Stacks.Sites.Conormal (kernelIdeal)
open Stacks.Sites.SqZeroPushout
open Stacks.Sites.SqZeroPullback
open Stacks.Sites.SqZeroExtension

universe u

namespace Stacks.Deformation.InverseImageExtension

variable {C : Type u} [SmallCategory C] {K : GrothendieckTopology C}
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- The setup of **Stacks 0GQ1**, read on `Y` as sheaves of commutative rings on a site: `A'` is
`g^{-1}𝒪_{X'}`, `A` is `g^{-1}𝒪_X`, `B'` is `𝒪_{Y'}`, `B` is `𝒪_Y` and `S` is
`g^{-1}f^{-1}𝒪_S`.  The square-zero ideal `g^{-1}ℱ` of `A'` is the kernel ideal of `π`, and `c`
is the map `g^{-1}ℱ ⟶ 𝒢` in the form the pushout of **Stacks 08UC** consumes. -/
structure Data (S A A' B B' : Sheaf K CommRingCat.{u}) where
  /-- The surjection `g^{-1}𝒪_{X'} ⟶ g^{-1}𝒪_X`. -/
  π : A' ⟶ A
  /-- It is locally surjective. -/
  locallySurjective_π : Presheaf.IsLocallySurjective K π.hom
  /-- The module `𝒢`, read over `g^{-1}𝒪_{X'}`. -/
  N : SheafOfModules.{u} (underlyingRingSheaf A')
  /-- The map `c : g^{-1}ℱ ⟶ 𝒢` out of the kernel ideal of `π`. -/
  c : PushoutData π N
  /-- The comorphism `g^♯ : g^{-1}𝒪_X ⟶ 𝒪_Y`. -/
  q : A ⟶ B
  /-- The surjection `𝒪_{Y'} ⟶ 𝒪_Y`. -/
  p : B' ⟶ B
  /-- It is locally surjective. -/
  locallySurjective_p : Presheaf.IsLocallySurjective K p.hom
  /-- The identification of `𝒢` with the kernel of `p`. -/
  ι : FibreInrData p N.val.presheaf
  /-- The ideal `𝒢` of `𝒪_{Y'}` squares to zero. -/
  inr_mul_inr (X : Cᵒᵖ) (n m : ↥((modules N).obj X)) : ι.app X n * ι.app X m = 0
  /-- The `g^{-1}𝒪_{X'}`-module structure of `𝒢` is the restriction, along `g^♯ ∘ π`, of the
  action of `𝒪_{Y'}` on its ideal `𝒢`. -/
  smul_inr (X : Cᵒᵖ) (b : ↥(B'.obj.obj X)) (a : ↥(A'.obj.obj X)) (n : ↥((modules N).obj X))
    (hb : p.hom.app X b = q.hom.app X (π.hom.app X a)) :
    b * ι.app X n = ι.app X (a • n)
  /-- The `g^{-1}f^{-1}𝒪_S`-algebra structure of `g^{-1}𝒪_{X'}`. -/
  u : S ⟶ A'
  /-- The `g^{-1}f^{-1}𝒪_S`-algebra structure of `𝒪_{Y'}`. -/
  v : S ⟶ B'
  /-- Both lie over `S`. -/
  base_comm : v ≫ p = (u ≫ π) ≫ q

attribute [instance] Data.locallySurjective_π Data.locallySurjective_p

/-- Two morphisms of sheaves of commutative rings are equal if they agree on all sections. -/
private theorem sheaf_hom_ext_app {C' : Type u} [SmallCategory C'] {K' : GrothendieckTopology C'}
    {R T : Sheaf K' CommRingCat.{u}} {f g : R ⟶ T}
    (h : ∀ (X : C'ᵒᵖ) (a : ↥(R.obj.obj X)), f.hom.app X a = g.hom.app X a) : f = g :=
  Sheaf.hom_ext (NatTrans.ext (funext fun X => CommRingCat.hom_ext (RingHom.ext (h X))))

/-- The inclusion of a sheaf of commutative rings into its trivial square-zero extension splits
the projection. -/
@[ega "0 18.2.3" "The canonical map g"]
theorem sqZeroExtSheafInl_comp_sqZeroExtSheafProj (R : Sheaf K CommRingCat.{u})
    (N : SheafOfModules.{u} (underlyingRingSheaf R)) :
    sqZeroExtSheafInl R N ≫ sqZeroExtSheafProj R N = 𝟙 R := by
  exact sheaf_hom_ext_app fun X r => rfl

namespace Data

variable {S A A' B B' : Sheaf K CommRingCat.{u}} (d : Data S A A' B B')

section Pullback

/-- The inclusion `𝒢 ⟶ 𝒪_{Y'}` of the ideal, with the sections of `𝒢` spelled as the sections
of the sheaf of modules `𝒢` rather than of its underlying presheaf of abelian groups. -/
def inr (X : Cᵒᵖ) : ↥((modules d.N).obj X) →+ ↥(B'.obj.obj X) := d.ι.app X

/-- The inclusion of the ideal commutes with the restriction maps. -/
theorem inr_map {X Y : Cᵒᵖ} (f : X ⟶ Y) (n : ↥((modules d.N).obj X)) :
    d.inr Y ((modules d.N).map f n) = (B'.obj.map f).hom (d.inr X n) := d.ι.app_map f n

/-- The identification of `𝒢` with the kernel of `p` lands in that kernel. -/
theorem p_app_inr (X : Cᵒᵖ) (n : ↥((modules d.N).obj X)) :
    d.p.hom.app X (d.inr X n) = 0 := (d.ι.range X _).2 ⟨n, rfl⟩

/-! The components of a local section of the trivial square-zero extension `g⁻¹𝒪_{X'} ⋉ 𝒢`,
restated for sections typed as sections of the *sheaf* `sqZeroExtSheaf A' d.N` rather than of
the presheaf of modules underneath it.  Each is `rfl`; they exist because the arithmetic of the
two spellings is carried by different instance terms, which blocks rewriting. -/

/-- The components of the unit section. -/
theorem extFst_one (X : Cᵒᵖ) :
    sqZeroExtFst (M := modules d.N) (1 : ↥((sqZeroExtSheaf A' d.N).obj.obj X)) = 1 := rfl

/-- The module component of the unit section vanishes. -/
theorem extSnd_one (X : Cᵒᵖ) :
    sqZeroExtSnd (M := modules d.N) (1 : ↥((sqZeroExtSheaf A' d.N).obj.obj X)) = 0 := rfl

/-- The ring component of the zero section vanishes. -/
theorem extFst_zero (X : Cᵒᵖ) :
    sqZeroExtFst (M := modules d.N) (0 : ↥((sqZeroExtSheaf A' d.N).obj.obj X)) = 0 := rfl

/-- The module component of the zero section vanishes. -/
theorem extSnd_zero (X : Cᵒᵖ) :
    sqZeroExtSnd (M := modules d.N) (0 : ↥((sqZeroExtSheaf A' d.N).obj.obj X)) = 0 := rfl

/-- The ring component is additive. -/
theorem extFst_add (X : Cᵒᵖ) (w w' : ↥((sqZeroExtSheaf A' d.N).obj.obj X)) :
    sqZeroExtFst (M := modules d.N) (w + w')
      = sqZeroExtFst (M := modules d.N) w + sqZeroExtFst (M := modules d.N) w' := rfl

/-- The module component is additive. -/
theorem extSnd_add (X : Cᵒᵖ) (w w' : ↥((sqZeroExtSheaf A' d.N).obj.obj X)) :
    sqZeroExtSnd (M := modules d.N) (w + w')
      = sqZeroExtSnd (M := modules d.N) w + sqZeroExtSnd (M := modules d.N) w' := rfl

/-- The ring component is multiplicative. -/
theorem extFst_mul (X : Cᵒᵖ) (w w' : ↥((sqZeroExtSheaf A' d.N).obj.obj X)) :
    sqZeroExtFst (M := modules d.N) (w * w')
      = sqZeroExtFst (M := modules d.N) w * sqZeroExtFst (M := modules d.N) w' := rfl

/-- The module component of a product, by the Leibniz rule. -/
theorem extSnd_mul (X : Cᵒᵖ) (w w' : ↥((sqZeroExtSheaf A' d.N).obj.obj X)) :
    sqZeroExtSnd (M := modules d.N) (w * w')
      = sqZeroExtFst (M := modules d.N) w • sqZeroExtSnd (M := modules d.N) w'
        + sqZeroExtFst (M := modules d.N) w' • sqZeroExtSnd (M := modules d.N) w := rfl

/-- Restriction acts on the ring component through `g^{-1}𝒪_{X'}`. -/
theorem extFst_map {X Y : Cᵒᵖ} (f : X ⟶ Y) (w : ↥((sqZeroExtSheaf A' d.N).obj.obj X)) :
    sqZeroExtFst (M := modules d.N) (((sqZeroExtSheaf A' d.N).obj.map f).hom w)
      = (A'.obj.map f).hom (sqZeroExtFst (M := modules d.N) w) := rfl

/-- Restriction acts on the module component through `𝒢`. -/
theorem extSnd_map {X Y : Cᵒᵖ} (f : X ⟶ Y) (w : ↥((sqZeroExtSheaf A' d.N).obj.obj X)) :
    sqZeroExtSnd (M := modules d.N) (((sqZeroExtSheaf A' d.N).obj.map f).hom w)
      = (modules d.N).map f (sqZeroExtSnd (M := modules d.N) w) := rfl

/-! ### The pullback extension `𝒪'₂ = 𝒪_{Y'} ×_{𝒪_Y} g⁻¹𝒪_X` -/

/-- **Stacks 0GQ2**, the second construction: pulling the extension
`0 ⟶ 𝒢 ⟶ 𝒪_{Y'} ⟶ 𝒪_Y ⟶ 0` back along `g^♯ : g^{-1}𝒪_X ⟶ 𝒪_Y` gives an extension
`0 ⟶ 𝒢 ⟶ 𝒪'₂ ⟶ g^{-1}𝒪_X ⟶ 0` of `g^{-1}f^{-1}𝒪_S`-algebras, with
`𝒪'₂ = 𝒪_{Y'} ×_{𝒪_Y} g^{-1}𝒪_X` the fibre product of sheaves of rings and the remark's second
displayed diagram its two projections. -/
@[stacks 0GQ2 "the pullback extension 𝒪'₂ = 𝒪_{Y'} ×_{𝒪_Y} g⁻¹𝒪_X, with the second displayed \
diagram its projections. Carried: that g⁻¹𝒪_{X'} is an extension of g⁻¹𝒪_X by g⁻¹ℱ, and that \
𝒢 is the square-zero ideal of 𝒪_{Y'} with its 𝒪_Y-action"]
def pullbackExtension : AlgebraExtension S A (d.u ≫ d.π) d.N.val.presheaf where
  O := fibreSheaf d.p d.q
  fromBase := fibreLift d.p d.q d.v (d.u ≫ d.π) d.base_comm
  proj := fibreSnd d.p d.q
  fromBase_comp_proj := fibreLift_comp_snd d.p d.q d.v (d.u ≫ d.π) d.base_comm
  locallySurjective := isLocallySurjective_fibreSnd d.p d.q
  inr X := fibreInrHom d.p d.q d.ι X
  inr_map f n := fibreInr_map d.p d.q d.ι f n
  inr_injective X := fibreInr_injective d.p d.q d.ι X
  proj_app_eq_zero_iff X s := fibreSnd_app_eq_zero_iff_exists_fibreInr d.p d.q d.ι X s
  inr_mul_inr X n m := fibreInr_mul_fibreInr d.p d.q d.ι X n m (d.inr_mul_inr X n m)

/-- The middle sheaf of the pullback extension is the fibre product. -/
theorem pullbackExtension_O : d.pullbackExtension.O = fibreSheaf d.p d.q := rfl

/-- The projection of the pullback extension is the second projection of the fibre product. -/
theorem pullbackExtension_proj : d.pullbackExtension.proj = fibreSnd d.p d.q := rfl

/-- The ideal of the pullback extension is included as `n ↦ (ι n, 0)`. -/
theorem pullbackExtension_inr (X : Cᵒᵖ) (n : ↥((modules d.N).obj X)) :
    d.pullbackExtension.inr X n = fibreInr d.p d.q d.ι X n := rfl

end Pullback

/-! ### The pushout extension `𝒪'₁` -/

section Pushout

variable [HasWeakSheafify K CommRingCat.{u}]

/-- **The map `g^{-1}𝒪_{X'} ⟶ 𝒪'₁`** of the first displayed diagram of **Stacks 0GQ2**:
`a ↦ [(a, 0)]`. -/
def pushoutMap : A' ⟶ pushoutSheaf d.π d.N d.c :=
  sqZeroExtSheafInl A' d.N ≫ pushoutMk d.π d.N d.c

/-- The map `g^{-1}𝒪_{X'} ⟶ 𝒪'₁` lies over `g^{-1}𝒪_X`. -/
theorem pushoutMap_comp_pushoutProj :
    d.pushoutMap ≫ pushoutProj d.π d.N d.c = d.π := by
  rw [pushoutMap, Category.assoc, pushoutMk_comp_pushoutProj, ← Category.assoc,
    sqZeroExtSheafInl_comp_sqZeroExtSheafProj A' d.N, Category.id_comp]

/-- The quotient map onto `𝒪'₁` is the sheafification unit applied to the class of a section of
the trivial square-zero extension. -/
theorem pushoutMk_app_eq_toSheafify (X : Cᵒᵖ)
    (w : ↥((sqZeroExtSheaf A' d.N).obj.obj X)) :
    (pushoutMk d.π d.N d.c).hom.app X w =
      (toSheafify K (Stacks.Sites.quotientPresheaf (graphIdealSubsheaf d.π d.N d.c))).app X
        (Ideal.Quotient.mk
          (Stacks.Sites.sectionIdeal (graphIdealSubsheaf d.π d.N d.c) X) w) := rfl

/-- The map `g^{-1}𝒪_{X'} ⟶ 𝒪'₁` on sections. -/
theorem pushoutMap_app (X : Cᵒᵖ) (a : ↥(A'.obj.obj X)) :
    d.pushoutMap.hom.app X a =
      (pushoutMk d.π d.N d.c).hom.app X
        (sqZeroExtMk (M := modules d.N) a (0 : ↥((modules d.N).obj X))) := rfl

/-- An antidiagonal section of the trivial square-zero extension dies in `𝒪'₁`. -/
theorem pushoutMk_app_graphSection (X : Cᵒᵖ) (g : ↥(kernelIdeal d.π.hom X)) :
    (pushoutMk d.π d.N d.c).hom.app X (graphSection d.π d.N d.c X g) = 0 := by
  rw [d.pushoutMk_app_eq_toSheafify X (graphSection d.π d.N d.c X g),
    show Ideal.Quotient.mk (Stacks.Sites.sectionIdeal (graphIdealSubsheaf d.π d.N d.c) X)
      (graphSection d.π d.N d.c X g) = 0 from Ideal.Quotient.eq_zero_iff_mem.2 ⟨g, rfl⟩]
  exact map_zero _

/-- **The map `g^{-1}𝒪_{X'} ⟶ 𝒪'₁` carries `g^{-1}ℱ` to `𝒢` by `c`.**  This is exactly the
relation imposed by the graph ideal: `(g, 0)` and `(0, c g)` differ by the antidiagonal section
of `g`. -/
theorem pushoutMap_app_kernel (X : Cᵒᵖ) (g : ↥(kernelIdeal d.π.hom X)) :
    d.pushoutMap.hom.app X (g : ↥(A'.obj.obj X)) =
      pushoutInr d.π d.N d.c X (d.c.app X g) := by
  have hsum : graphSection d.π d.N d.c X g + inrSection d.N X (d.c.app X g) =
      sqZeroExtMk (M := modules d.N) (g : ↥(A'.obj.obj X)) (0 : ↥((modules d.N).obj X)) := by
    refine sqZeroExt_ext ?_ ?_
    · rw [sqZeroExtFst_add, graphSection_fst, inrSection_fst, add_zero, sqZeroExtFst_mk]
    · rw [sqZeroExtSnd_add, graphSection_snd, inrSection_snd, sqZeroExtSnd_mk, neg_add_cancel]
  have e1 : (pushoutMk d.π d.N d.c).hom.app X
        (sqZeroExtMk (M := modules d.N) (g : ↥(A'.obj.obj X)) (0 : ↥((modules d.N).obj X)))
      = (pushoutMk d.π d.N d.c).hom.app X
          (graphSection d.π d.N d.c X g + inrSection d.N X (d.c.app X g)) :=
    congrArg (ConcreteCategory.hom ((pushoutMk d.π d.N d.c).hom.app X)) hsum.symm
  refine (d.pushoutMap_app X (g : ↥(A'.obj.obj X))).trans (e1.trans ?_)
  refine (map_add (ConcreteCategory.hom ((pushoutMk d.π d.N d.c).hom.app X))
    (graphSection d.π d.N d.c X g) (inrSection d.N X (d.c.app X g))).trans ?_
  exact (congrArg
    (fun z => z + (pushoutMk d.π d.N d.c).hom.app X (inrSection d.N X (d.c.app X g)))
    (d.pushoutMk_app_graphSection X g)).trans (zero_add _)

/-- **Stacks 0GQ2**, the first construction: pushing the extension
`0 ⟶ g^{-1}ℱ ⟶ g^{-1}𝒪_{X'} ⟶ g^{-1}𝒪_X ⟶ 0` out along `c : g^{-1}ℱ ⟶ 𝒢` gives an extension
`0 ⟶ 𝒢 ⟶ 𝒪'₁ ⟶ g^{-1}𝒪_X ⟶ 0` of `g^{-1}f^{-1}𝒪_S`-algebras, with the remark's first
displayed diagram its comparison with `g^{-1}𝒪_{X'}`. -/
@[stacks 0GQ2 "the pushout extension 𝒪'₁ of g⁻¹𝒪_{X'} along c, with the first displayed diagram \
its comparison with g⁻¹𝒪_{X'}. Carried: that g⁻¹𝒪_{X'} is an extension of g⁻¹𝒪_X by g⁻¹ℱ, the \
ideal being Ker π"]
def pushoutExtension [K.WEqualsLocallyBijective CommRingCat.{u}] :
    AlgebraExtension S A (d.u ≫ d.π) d.N.val.presheaf where
  O := pushoutSheaf d.π d.N d.c
  fromBase := d.u ≫ d.pushoutMap
  proj := pushoutProj d.π d.N d.c
  fromBase_comp_proj := by rw [Category.assoc, d.pushoutMap_comp_pushoutProj]
  locallySurjective := isLocallySurjective_pushoutProj d.π d.N d.c
  inr X := pushoutInrHom d.π d.N d.c X
  inr_map f n := pushoutInr_map d.π d.N d.c f n
  inr_injective X := pushoutInr_injective d.π d.N d.c X
  proj_app_eq_zero_iff X s := pushoutProj_app_eq_zero_iff d.π d.N d.c X s
  inr_mul_inr X n m := pushoutInr_mul_pushoutInr d.π d.N d.c X n m

section WeakSheafify

variable [K.WEqualsLocallyBijective CommRingCat.{u}]

/-- The middle sheaf of the pushout extension is the square-zero pushout. -/
theorem pushoutExtension_O : d.pushoutExtension.O = pushoutSheaf d.π d.N d.c := rfl

/-- The projection of the pushout extension. -/
theorem pushoutExtension_proj : d.pushoutExtension.proj = pushoutProj d.π d.N d.c := rfl

/-- The ideal of the pushout extension is included as `n ↦ [(0, n)]`. -/
theorem pushoutExtension_inr (X : Cᵒᵖ) (n : ↥((modules d.N).obj X)) :
    d.pushoutExtension.inr X n = pushoutInr d.π d.N d.c X n := rfl

/-- The structure morphism of the pushout extension. -/
theorem pushoutExtension_fromBase : d.pushoutExtension.fromBase = d.u ≫ d.pushoutMap := rfl

end WeakSheafify

end Pushout

/-! ### The criterion of Stacks 0GQ2 -/

section Comparison

variable [HasWeakSheafify K CommRingCat.{u}]

/-- An `S`-morphism `Y' → X'` compatible with `g` and `c`: a morphism
`h : g^{-1}𝒪_{X'} ⟶ 𝒪_{Y'}` of `g^{-1}f^{-1}𝒪_S`-algebras which lies over `g^♯` and whose
restriction to the ideal `g^{-1}ℱ` is `c`. -/
structure CompatibleHom where
  /-- The morphism `g^{-1}𝒪_{X'} ⟶ 𝒪_{Y'}`. -/
  hom : A' ⟶ B'
  /-- It is a morphism of `g^{-1}f^{-1}𝒪_S`-algebras. -/
  base_comm : d.u ≫ hom = d.v
  /-- It lies over `g^♯`. -/
  proj_comm : hom ≫ d.p = d.π ≫ d.q
  /-- Its restriction to the ideal `g^{-1}ℱ = Ker π` is `c`. -/
  kernel_comm (X : Cᵒᵖ) (g : ↥(kernelIdeal d.π.hom X)) :
    hom.hom.app X (g : ↥(A'.obj.obj X)) = d.inr X (d.c.app X g)

omit [HasWeakSheafify K CommRingCat.{u}] in
/-- A compatible morphism lies over `g^♯`, on sections. -/
theorem compatibleHom_p_app (h : d.CompatibleHom) (X : Cᵒᵖ) (a : ↥(A'.obj.obj X)) :
    d.p.hom.app X (h.hom.hom.app X a) = d.q.hom.app X (d.π.hom.app X a) :=
  congrArg (fun t : A' ⟶ B => t.hom.app X a) h.proj_comm

/-- The map `g^{-1}𝒪_{X'} ⋉ 𝒢 ⟶ 𝒪_{Y'}` attached to a compatible morphism `h`, on sections:
`(a, n) ↦ h a + ι n`.  It is multiplicative because the ideal `𝒢` of `𝒪_{Y'}` squares to zero
and because `h a` acts on it through `g^♯ ∘ π`. -/
def comparisonFirstApp (h : d.CompatibleHom) (X : Cᵒᵖ) :
    ↥((sqZeroExtSheaf A' d.N).obj.obj X) →+* ↥(B'.obj.obj X) where
  toFun w := h.hom.hom.app X (sqZeroExtFst (M := modules d.N) w)
    + d.inr X (sqZeroExtSnd (M := modules d.N) w)
  map_one' := by
    change h.hom.hom.app X (sqZeroExtFst (M := modules d.N)
          (1 : ↥((sqZeroExtSheaf A' d.N).obj.obj X)))
        + d.inr X (sqZeroExtSnd (M := modules d.N)
          (1 : ↥((sqZeroExtSheaf A' d.N).obj.obj X))) = 1
    rw [d.extFst_one X, d.extSnd_one X, map_one, map_zero, add_zero]
  map_zero' := by
    change h.hom.hom.app X (sqZeroExtFst (M := modules d.N)
          (0 : ↥((sqZeroExtSheaf A' d.N).obj.obj X)))
        + d.inr X (sqZeroExtSnd (M := modules d.N)
          (0 : ↥((sqZeroExtSheaf A' d.N).obj.obj X))) = 0
    rw [d.extFst_zero X, d.extSnd_zero X, map_zero, map_zero, add_zero]
  map_add' w w' := by
    change h.hom.hom.app X (sqZeroExtFst (M := modules d.N) (w + w'))
        + d.inr X (sqZeroExtSnd (M := modules d.N) (w + w'))
      = (h.hom.hom.app X (sqZeroExtFst (M := modules d.N) w)
          + d.inr X (sqZeroExtSnd (M := modules d.N) w))
        + (h.hom.hom.app X (sqZeroExtFst (M := modules d.N) w')
          + d.inr X (sqZeroExtSnd (M := modules d.N) w'))
    rw [d.extFst_add X w w', d.extSnd_add X w w', map_add, map_add]
    abel
  map_mul' w w' := by
    have e1 : h.hom.hom.app X (sqZeroExtFst (M := modules d.N) w)
          * d.inr X (sqZeroExtSnd (M := modules d.N) w')
        = d.inr X (sqZeroExtFst (M := modules d.N) w • sqZeroExtSnd (M := modules d.N) w') :=
      d.smul_inr X _ _ _ (d.compatibleHom_p_app h X (sqZeroExtFst (M := modules d.N) w))
    have e2 : h.hom.hom.app X (sqZeroExtFst (M := modules d.N) w')
          * d.inr X (sqZeroExtSnd (M := modules d.N) w)
        = d.inr X (sqZeroExtFst (M := modules d.N) w' • sqZeroExtSnd (M := modules d.N) w) :=
      d.smul_inr X _ _ _ (d.compatibleHom_p_app h X (sqZeroExtFst (M := modules d.N) w'))
    have e3 : d.inr X (sqZeroExtSnd (M := modules d.N) w)
        * d.inr X (sqZeroExtSnd (M := modules d.N) w') = 0 :=
      d.inr_mul_inr X _ _
    change h.hom.hom.app X (sqZeroExtFst (M := modules d.N) (w * w'))
        + d.inr X (sqZeroExtSnd (M := modules d.N) (w * w'))
      = (h.hom.hom.app X (sqZeroExtFst (M := modules d.N) w)
          + d.inr X (sqZeroExtSnd (M := modules d.N) w))
        * (h.hom.hom.app X (sqZeroExtFst (M := modules d.N) w')
          + d.inr X (sqZeroExtSnd (M := modules d.N) w'))
    rw [d.extFst_mul X w w', d.extSnd_mul X w w', map_mul, map_add, ← e1, ← e2]
    linear_combination -e3

/-- The map `g^{-1}𝒪_{X'} ⋉ 𝒢 ⟶ 𝒪_{Y'}` attached to a compatible morphism. -/
def comparisonFirst (h : d.CompatibleHom) : (sqZeroExtSheaf A' d.N).obj ⟶ B'.obj where
  app X := CommRingCat.ofHom (R := ↥((sqZeroExtSheaf A' d.N).obj.obj X))
    (S := ↥(B'.obj.obj X)) (d.comparisonFirstApp h X)
  naturality X Y f := by
    apply CommRingCat.hom_ext
    refine RingHom.ext fun w => ?_
    change h.hom.hom.app Y (sqZeroExtFst (M := modules d.N)
          (((sqZeroExtSheaf A' d.N).obj.map f).hom w))
        + d.inr Y (sqZeroExtSnd (M := modules d.N)
          (((sqZeroExtSheaf A' d.N).obj.map f).hom w))
      = (B'.obj.map f).hom (h.hom.hom.app X (sqZeroExtFst (M := modules d.N) w)
          + d.inr X (sqZeroExtSnd (M := modules d.N) w))
    rw [d.extFst_map f w, d.extSnd_map f w]
    exact (congrArg₂ (· + ·)
      (NatTrans.naturality_apply h.hom.hom f (sqZeroExtFst (M := modules d.N) w))
      (d.inr_map f (sqZeroExtSnd (M := modules d.N) w))).trans
        (map_add (ConcreteCategory.hom (B'.obj.map f)) _ _).symm

/-- The map `g^{-1}𝒪_{X'} ⋉ 𝒢 ⟶ 𝒪'₂` attached to a compatible morphism:
`(a, n) ↦ (h a + ι n, π a)`.  The two components agree over `𝒪_Y` because `h` lies over `g^♯`
and `ι` lands in the kernel of `p`. -/
def comparisonSqZero (h : d.CompatibleHom) :
    (sqZeroExtSheaf A' d.N).obj ⟶ (fibreSheaf d.p d.q).obj :=
  fibrePresheafLift d.p d.q (d.comparisonFirst h) (sqZeroExtSheafProj A' d.N ≫ d.π).hom (by
    refine NatTrans.ext (funext fun X => CommRingCat.hom_ext (RingHom.ext fun w => ?_))
    change d.p.hom.app X (h.hom.hom.app X (sqZeroExtFst (M := modules d.N) w)
          + d.inr X (sqZeroExtSnd (M := modules d.N) w))
      = d.q.hom.app X (d.π.hom.app X (sqZeroExtFst (M := modules d.N) w))
    rw [map_add, d.compatibleHom_p_app h X (sqZeroExtFst (M := modules d.N) w),
      d.p_app_inr X (sqZeroExtSnd (M := modules d.N) w), add_zero])

omit [HasWeakSheafify K CommRingCat.{u}] in
/-- The components of the comparison out of the trivial square-zero extension. -/
theorem fibreVal_comparisonSqZero (h : d.CompatibleHom) (X : Cᵒᵖ)
    (w : ↥((sqZeroExtSheaf A' d.N).obj.obj X)) :
    fibreVal d.p d.q X ((d.comparisonSqZero h).app X w)
      = (h.hom.hom.app X (sqZeroExtFst (M := modules d.N) w)
          + d.inr X (sqZeroExtSnd (M := modules d.N) w),
        d.π.hom.app X (sqZeroExtFst (M := modules d.N) w)) := rfl

omit [HasWeakSheafify K CommRingCat.{u}] in
/-- The comparison out of the trivial square-zero extension kills the graph ideal of `c`: the
antidiagonal section of `g` goes to `(h g - ι (c g), π g) = (0, 0)`. -/
theorem comparisonSqZero_app_graphSection (h : d.CompatibleHom) (X : Cᵒᵖ)
    (g : ↥(kernelIdeal d.π.hom X)) :
    (d.comparisonSqZero h).app X (graphSection d.π d.N d.c X g) = 0 := by
  refine fibreVal_injective d.p d.q X (Prod.ext ?_ ?_)
  · show h.hom.hom.app X (sqZeroExtFst (M := modules d.N) (graphSection d.π d.N d.c X g))
        + d.inr X (sqZeroExtSnd (M := modules d.N) (graphSection d.π d.N d.c X g)) = 0
    rw [graphSection_fst, graphSection_snd, h.kernel_comm X g, map_neg, add_neg_cancel]
  · show d.π.hom.app X (sqZeroExtFst (M := modules d.N) (graphSection d.π d.N d.c X g)) = 0
    rw [graphSection_fst]
    exact g.2

/-- The comparison `(g^{-1}𝒪_{X'} ⋉ 𝒢)/J ⟶ 𝒪'₂` on the objectwise quotient by the graph
ideal. -/
def comparisonQuotient (h : d.CompatibleHom) :
    Stacks.Sites.quotientPresheaf (graphIdealSubsheaf d.π d.N d.c)
      ⟶ (fibreSheaf d.p d.q).obj where
  app X := CommRingCat.ofHom
    (R := ↥((Stacks.Sites.quotientPresheaf (graphIdealSubsheaf d.π d.N d.c)).obj X))
    (S := ↥((fibreSheaf d.p d.q).obj.obj X))
    (Ideal.Quotient.lift (Stacks.Sites.sectionIdeal (graphIdealSubsheaf d.π d.N d.c) X)
      ((d.comparisonSqZero h).app X).hom (by
        rintro _ ⟨g, rfl⟩
        exact d.comparisonSqZero_app_graphSection h X g))
  naturality X Y f := by
    apply CommRingCat.hom_ext
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun w => ?_)
    exact NatTrans.naturality_apply (d.comparisonSqZero h) f w

/-- **The comparison `𝒪'₁ ⟶ 𝒪'₂`** attached to a compatible morphism `h`, obtained from the
objectwise comparison by the universal property of sheafification. -/
def comparisonHom (h : d.CompatibleHom) :
    pushoutSheaf d.π d.N d.c ⟶ fibreSheaf d.p d.q :=
  ⟨sheafifyLift K (d.comparisonQuotient h) (fibreSheaf d.p d.q).property⟩

/-- The comparison `𝒪'₁ ⟶ 𝒪'₂`, computed on the class of a section of the trivial square-zero
extension. -/
theorem comparisonHom_app_pushoutMk (h : d.CompatibleHom) (X : Cᵒᵖ)
    (w : ↥((sqZeroExtSheaf A' d.N).obj.obj X)) :
    (d.comparisonHom h).hom.app X ((pushoutMk d.π d.N d.c).hom.app X w)
      = (d.comparisonSqZero h).app X w :=
  congrArg (fun α : Stacks.Sites.quotientPresheaf (graphIdealSubsheaf d.π d.N d.c)
      ⟶ (fibreSheaf d.p d.q).obj =>
    α.app X (Ideal.Quotient.mk
      (Stacks.Sites.sectionIdeal (graphIdealSubsheaf d.π d.N d.c) X) w))
    (toSheafify_sheafifyLift K (d.comparisonQuotient h) (fibreSheaf d.p d.q).property)

/-- The comparison `𝒪'₁ ⟶ 𝒪'₂` on the image of `g^{-1}𝒪_{X'}`. -/
theorem comparisonHom_app_pushoutMap (h : d.CompatibleHom) (X : Cᵒᵖ) (a : ↥(A'.obj.obj X)) :
    (d.comparisonHom h).hom.app X (d.pushoutMap.hom.app X a)
      = (d.comparisonSqZero h).app X
          (sqZeroExtMk (M := modules d.N) a (0 : ↥((modules d.N).obj X))) :=
  d.comparisonHom_app_pushoutMk h X _

/-- The comparison `𝒪'₁ ⟶ 𝒪'₂` is the identity on the ideal `𝒢`. -/
theorem comparisonHom_app_pushoutInr (h : d.CompatibleHom) (X : Cᵒᵖ)
    (n : ↥((modules d.N).obj X)) :
    (d.comparisonHom h).hom.app X (pushoutInr d.π d.N d.c X n)
      = fibreInr d.p d.q d.ι X n := by
  refine (d.comparisonHom_app_pushoutMk h X (inrSection d.N X n)).trans ?_
  refine fibreVal_injective d.p d.q X (Prod.ext ?_ ?_)
  · show h.hom.hom.app X (sqZeroExtFst (M := modules d.N) (inrSection d.N X n))
        + d.inr X (sqZeroExtSnd (M := modules d.N) (inrSection d.N X n)) = d.inr X n
    rw [inrSection_fst, inrSection_snd, map_zero, zero_add]
  · show d.π.hom.app X (sqZeroExtFst (M := modules d.N) (inrSection d.N X n)) = 0
    rw [inrSection_fst, map_zero]

/-- Composing `g^{-1}𝒪_{X'} ⟶ 𝒪'₁ ⟶ 𝒪'₂` with the projection onto `𝒪_{Y'}` returns `h`. -/
theorem pushoutMap_comp_comparisonHom_comp_fibreFst (h : d.CompatibleHom) :
    d.pushoutMap ≫ d.comparisonHom h ≫ fibreFst d.p d.q = h.hom := by
  refine sheaf_hom_ext_app fun X a => ?_
  refine Eq.trans (congrArg ((fibreFst d.p d.q).hom.app X)
    (d.comparisonHom_app_pushoutMap h X a)) ?_
  show h.hom.hom.app X a + d.inr X (0 : ↥((modules d.N).obj X)) = h.hom.hom.app X a
  rw [map_zero, add_zero]

/-- Composing `g^{-1}𝒪_{X'} ⟶ 𝒪'₁ ⟶ 𝒪'₂` with the projection onto `g^{-1}𝒪_X` returns `π`. -/
theorem pushoutMap_comp_comparisonHom_comp_fibreSnd (h : d.CompatibleHom) :
    d.pushoutMap ≫ d.comparisonHom h ≫ fibreSnd d.p d.q = d.π := by
  refine sheaf_hom_ext_app fun X a => ?_
  exact Eq.trans (congrArg ((fibreSnd d.p d.q).hom.app X)
    (d.comparisonHom_app_pushoutMap h X a)) rfl

/-- The comparison `𝒪'₁ ⟶ 𝒪'₂` lies over `g^{-1}𝒪_X`: both it followed by the projection of
`𝒪'₂` and the projection of `𝒪'₁` restrict along the sheafification unit to the same objectwise
map, namely `[w] ↦ π w₁`. -/
theorem comparisonHom_comp_fibreSnd (h : d.CompatibleHom) :
    d.comparisonHom h ≫ fibreSnd d.p d.q = pushoutProj d.π d.N d.c := by
  have key : d.comparisonQuotient h ≫ fibreSndHom d.p d.q = quotientToTarget d.π d.N d.c := by
    refine NatTrans.ext (funext fun X => CommRingCat.hom_ext ?_)
    exact Ideal.Quotient.ringHom_ext (RingHom.ext fun w => rfl)
  have e0 : toSheafify K (Stacks.Sites.quotientPresheaf (graphIdealSubsheaf d.π d.N d.c))
      ≫ (d.comparisonHom h).hom = d.comparisonQuotient h :=
    toSheafify_sheafifyLift K (d.comparisonQuotient h) (fibreSheaf d.p d.q).property
  have e1 : toSheafify K (Stacks.Sites.quotientPresheaf (graphIdealSubsheaf d.π d.N d.c))
      ≫ ((d.comparisonHom h).hom ≫ (fibreSnd d.p d.q).hom)
      = quotientToTarget d.π d.N d.c :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun α : Stacks.Sites.quotientPresheaf (graphIdealSubsheaf d.π d.N d.c)
        ⟶ (fibreSheaf d.p d.q).obj => α ≫ fibreSndHom d.p d.q) e0).trans key)
  have e2 : toSheafify K (Stacks.Sites.quotientPresheaf (graphIdealSubsheaf d.π d.N d.c))
      ≫ (pushoutProj d.π d.N d.c).hom = quotientToTarget d.π d.N d.c :=
    toSheafify_sheafifyLift K (quotientToTarget d.π d.N d.c) A.property
  exact Sheaf.hom_ext (sheafify_hom_ext K _ _ A.property (e1.trans e2.symm))

section Extensions

variable [K.WEqualsLocallyBijective CommRingCat.{u}]

/-- **The comparison `𝒪'₁ ⟶ 𝒪'₂` is a morphism of extensions** of `g^{-1}𝒪_X` by `𝒢` over
`g^{-1}f^{-1}𝒪_S`. -/
def comparisonExtensionHom (h : d.CompatibleHom) :
    AlgebraExtension.Hom d.pushoutExtension d.pullbackExtension where
  hom := d.comparisonHom h
  base_comm := by
    change (d.u ≫ d.pushoutMap) ≫ d.comparisonHom h
      = fibreLift d.p d.q d.v (d.u ≫ d.π) d.base_comm
    refine fibre_hom_ext d.p d.q ?_ ?_
    · rw [Category.assoc, Category.assoc, d.pushoutMap_comp_comparisonHom_comp_fibreFst h,
        h.base_comm, fibreLift_comp_fst]
    · rw [Category.assoc, Category.assoc, d.pushoutMap_comp_comparisonHom_comp_fibreSnd h,
        fibreLift_comp_snd]
  proj_comm := d.comparisonHom_comp_fibreSnd h
  inr_comm X n := d.comparisonHom_app_pushoutInr h X n

/-- A morphism of extensions `𝒪'₁ ⟶ 𝒪'₂`, read in the concrete spelling of the two
constructions rather than through the middle sheaves of the packaged extensions. -/
def extensionHomMap (e : AlgebraExtension.Hom d.pushoutExtension d.pullbackExtension) :
    pushoutSheaf d.π d.N d.c ⟶ fibreSheaf d.p d.q := e.hom

/-- A morphism of extensions is a morphism of `g^{-1}f^{-1}𝒪_S`-algebras. -/
theorem extensionHomMap_base
    (e : AlgebraExtension.Hom d.pushoutExtension d.pullbackExtension) :
    (d.u ≫ d.pushoutMap) ≫ d.extensionHomMap e
      = fibreLift d.p d.q d.v (d.u ≫ d.π) d.base_comm := e.base_comm

/-- A morphism of extensions lies over `g^{-1}𝒪_X`. -/
theorem extensionHomMap_proj
    (e : AlgebraExtension.Hom d.pushoutExtension d.pullbackExtension) :
    d.extensionHomMap e ≫ fibreSnd d.p d.q = pushoutProj d.π d.N d.c := e.proj_comm

/-- A morphism of extensions is the identity on the ideal `𝒢`. -/
theorem extensionHomMap_inr
    (e : AlgebraExtension.Hom d.pushoutExtension d.pullbackExtension) (X : Cᵒᵖ)
    (n : ↥((modules d.N).obj X)) :
    (d.extensionHomMap e).hom.app X (pushoutInr d.π d.N d.c X n)
      = fibreInr d.p d.q d.ι X n := e.inr_comm X n

/-- **The compatible morphism attached to a morphism of extensions**: compose
`g^{-1}𝒪_{X'} ⟶ 𝒪'₁` with it and with the projection `𝒪'₂ ⟶ 𝒪_{Y'}`. -/
def compatibleHomOfExtensionHom
    (e : AlgebraExtension.Hom d.pushoutExtension d.pullbackExtension) : d.CompatibleHom where
  hom := d.pushoutMap ≫ d.extensionHomMap e ≫ fibreFst d.p d.q
  base_comm := by
    calc d.u ≫ (d.pushoutMap ≫ d.extensionHomMap e ≫ fibreFst d.p d.q)
        = ((d.u ≫ d.pushoutMap) ≫ d.extensionHomMap e) ≫ fibreFst d.p d.q := by
          rw [Category.assoc, Category.assoc]
      _ = d.v := by rw [d.extensionHomMap_base e, fibreLift_comp_fst]
  proj_comm := by
    calc (d.pushoutMap ≫ d.extensionHomMap e ≫ fibreFst d.p d.q) ≫ d.p
        = d.pushoutMap ≫ d.extensionHomMap e ≫ fibreSnd d.p d.q ≫ d.q := by
          rw [Category.assoc, Category.assoc, fibreFst_comp_eq]
      _ = d.π ≫ d.q := by
          rw [← Category.assoc (d.extensionHomMap e), d.extensionHomMap_proj e,
            ← Category.assoc, d.pushoutMap_comp_pushoutProj]
  kernel_comm X g := by
    refine Eq.trans (congrArg
      (fun z => (fibreFst d.p d.q).hom.app X ((d.extensionHomMap e).hom.app X z))
      (d.pushoutMap_app_kernel X g)) ?_
    exact congrArg ((fibreFst d.p d.q).hom.app X) (d.extensionHomMap_inr e X (d.c.app X g))

/-- **The two directions of the criterion are mutually inverse on the underlying morphisms.**
A compatible morphism `h`, turned into a morphism of extensions and back, is `h` again: the
morphism of extensions produced from `h` remembers `h`. -/
theorem compatibleHomOfExtensionHom_comparisonExtensionHom (h : d.CompatibleHom) :
    (d.compatibleHomOfExtensionHom (d.comparisonExtensionHom h)).hom = h.hom :=
  d.pushoutMap_comp_comparisonHom_comp_fibreFst h

/-- **Stacks 0GQ2**, the criterion.  An `S`-morphism `Y' → X'` compatible with `g` and `c`
exists if and only if the pushout `𝒪'₁` and the pullback `𝒪'₂` are isomorphic as
`g^{-1}f^{-1}𝒪_S`-algebra extensions of `g^{-1}𝒪_X` by `𝒢`. -/
@[stacks 0GQ2 "the diagram chase: a compatible S-morphism Y' → X' exists iff 𝒪'₁ ≅ 𝒪'₂ as \
g⁻¹f⁻¹𝒪_S-algebra extensions of g⁻¹𝒪_X by 𝒢. Carried: that g⁻¹𝒪_{X'} is an extension of \
g⁻¹𝒪_X by g⁻¹ℱ, and that 𝒢 is the square-zero ideal of 𝒪_{Y'} with its 𝒪_Y-action"]
theorem nonempty_compatibleHom_iff_isomorphic :
    Nonempty d.CompatibleHom ↔
      AlgebraExtension.Isomorphic d.pushoutExtension d.pullbackExtension :=
  ⟨fun h => ⟨d.comparisonExtensionHom (Nonempty.some h)⟩,
    fun e => ⟨d.compatibleHomOfExtensionHom (Nonempty.some e)⟩⟩

end Extensions

end Comparison

end Data

/-! ### An example in which both sides of the criterion hold

Over any sheaf of commutative rings `R` on any site and any sheaf of
`R`-modules `𝒢`, take `g^{-1}𝒪_{X'} = g^{-1}𝒪_X = 𝒪_Y = g^{-1}f^{-1}𝒪_S = R` with `π`, `q` and
the two algebra structures the identity, and `𝒪_{Y'} = R ⋉ 𝒢` the trivial square-zero extension
with `p` its projection.  Then `g^{-1}ℱ = Ker π = 0`, `c = 0`, and the zero section
`R ⟶ R ⋉ 𝒢` is a compatible `S`-morphism, so both sides of the criterion hold. -/

section Witness

variable [HasWeakSheafify K CommRingCat.{u}] [K.WEqualsLocallyBijective CommRingCat.{u}]
  (R : Sheaf K CommRingCat.{u}) (N : SheafOfModules.{u} (underlyingRingSheaf R))

omit [HasWeakSheafify K CommRingCat.{u}] [K.WEqualsLocallyBijective CommRingCat.{u}] in
/-- The identity of a sheaf of commutative rings is locally surjective. -/
instance isLocallySurjective_id : Presheaf.IsLocallySurjective K (𝟙 R : R ⟶ R).hom where
  imageSieve_mem {X} r := by
    refine K.superset_covering (fun Y f _ => ?_) (K.top_mem X)
    exact ⟨(R.obj.map f.op).hom r, rfl⟩

omit [HasWeakSheafify K CommRingCat.{u}] [K.WEqualsLocallyBijective CommRingCat.{u}] in
/-- The projection of a trivial square-zero extension is locally surjective, being surjective
on sections. -/
instance isLocallySurjective_sqZeroExtSheafProj :
    Presheaf.IsLocallySurjective K (sqZeroExtSheafProj R N).hom where
  imageSieve_mem {X} r := by
    refine K.superset_covering (fun Y f _ => ?_) (K.top_mem X)
    exact ⟨sqZeroExtMk (M := modules N) ((R.obj.map f.op).hom r)
      (0 : ↥((modules N).obj (op Y))), rfl⟩

omit [HasWeakSheafify K CommRingCat.{u}] [K.WEqualsLocallyBijective CommRingCat.{u}] in
/-- The inclusion of `𝒢` into `R ⋉ 𝒢`, as a homomorphism of additive groups of sections. -/
def trivialInrHom (X : Cᵒᵖ) :
    ↥((modules N).obj X) →+ ↥((sqZeroExtSheaf R N).obj.obj X) where
  toFun := inrSection N X
  map_zero' := inrSection_zero N X
  map_add' := inrSection_add N X

omit [HasWeakSheafify K CommRingCat.{u}] [K.WEqualsLocallyBijective CommRingCat.{u}] in
/-- The ring component of a pure-`𝒢` section vanishes. -/
theorem trivialInrHom_fst (X : Cᵒᵖ) (n : ↥((modules N).obj X)) :
    sqZeroExtFst (M := modules N) (trivialInrHom R N X n) = 0 := inrSection_fst N X n

omit [HasWeakSheafify K CommRingCat.{u}] [K.WEqualsLocallyBijective CommRingCat.{u}] in
/-- The module component of a pure-`𝒢` section is the section it comes from. -/
theorem trivialInrHom_snd (X : Cᵒᵖ) (n : ↥((modules N).obj X)) :
    sqZeroExtSnd (M := modules N) (trivialInrHom R N X n) = n := inrSection_snd N X n

omit [HasWeakSheafify K CommRingCat.{u}] [K.WEqualsLocallyBijective CommRingCat.{u}] in
/-- Multiplying a pure-`𝒢` section of `R ⋉ 𝒢` by a local section acts through `R`. -/
theorem mul_trivialInrHom (X : Cᵒᵖ) (b : ↥((sqZeroExtSheaf R N).obj.obj X))
    (n : ↥((modules N).obj X)) :
    b * trivialInrHom R N X n
      = trivialInrHom R N X (sqZeroExtFst (M := modules N) b • n) := by
  refine sqZeroExt_ext ?_ ?_
  · show sqZeroExtFst (M := modules N) b * sqZeroExtFst (M := modules N)
        (trivialInrHom R N X n)
      = sqZeroExtFst (M := modules N)
        (trivialInrHom R N X (sqZeroExtFst (M := modules N) b • n))
    rw [trivialInrHom_fst, trivialInrHom_fst, mul_zero]
  · show sqZeroExtFst (M := modules N) b • sqZeroExtSnd (M := modules N)
          (trivialInrHom R N X n)
        + sqZeroExtFst (M := modules N) (trivialInrHom R N X n) • sqZeroExtSnd (M := modules N) b
      = sqZeroExtSnd (M := modules N)
        (trivialInrHom R N X (sqZeroExtFst (M := modules N) b • n))
    rw [trivialInrHom_fst, trivialInrHom_snd, trivialInrHom_snd, zero_smul, add_zero]

omit [HasWeakSheafify K CommRingCat.{u}] [K.WEqualsLocallyBijective CommRingCat.{u}] in
/-- The ideal `𝒢` of `R ⋉ 𝒢` has square zero. -/
theorem trivialInrHom_mul_trivialInrHom (X : Cᵒᵖ) (n m : ↥((modules N).obj X)) :
    trivialInrHom R N X n * trivialInrHom R N X m = 0 := by
  rw [mul_trivialInrHom, trivialInrHom_fst, zero_smul, map_zero]

omit [HasWeakSheafify K CommRingCat.{u}] [K.WEqualsLocallyBijective CommRingCat.{u}] in
/-- `𝒢` is the ideal of the trivial square-zero extension `R ⋉ 𝒢`. -/
def trivialFibreInrData : FibreInrData (sqZeroExtSheafProj R N) N.val.presheaf where
  app X := trivialInrHom R N X
  app_map f n := (sqZeroExtMap_inrSection N f n).symm
  app_injective X n m hnm :=
    (trivialInrHom_snd R N X n).symm.trans
      ((congrArg (sqZeroExtSnd (M := modules N)) hnm).trans (trivialInrHom_snd R N X m))
  range X w :=
    ⟨fun hw => ⟨sqZeroExtSnd (M := modules N) w,
      sqZeroExt_ext ((trivialInrHom_fst R N X _).trans hw.symm)
        (trivialInrHom_snd R N X _)⟩,
      fun hw => hw.elim fun n hn => hn ▸ trivialInrHom_fst R N X n⟩

omit [HasWeakSheafify K CommRingCat.{u}] [K.WEqualsLocallyBijective CommRingCat.{u}] in
/-- The zero map out of `Ker (𝟙 R) = 0`, which is the map `c` of the witness. -/
def trivialPushoutData : PushoutData (𝟙 R : R ⟶ R) N where
  app X := 0
  app_smul X r g := (smul_zero r).symm
  app_map f g := (map_zero ((modules N).presheaf.map f).hom).symm
  smul_eq_zero X g m := by
    have hg : (g : ↥(R.obj.obj X)) = 0 := g.2
    rw [hg, zero_smul]

/-- **The witness setup**: `g^{-1}𝒪_{X'} = g^{-1}𝒪_X = 𝒪_Y = g^{-1}f^{-1}𝒪_S = R` and
`𝒪_{Y'} = R ⋉ 𝒢`. -/
def trivialData : Data R R R R (sqZeroExtSheaf R N) where
  π := 𝟙 R
  locallySurjective_π := isLocallySurjective_id R
  N := N
  c := trivialPushoutData R N
  q := 𝟙 R
  p := sqZeroExtSheafProj R N
  locallySurjective_p := isLocallySurjective_sqZeroExtSheafProj R N
  ι := trivialFibreInrData R N
  inr_mul_inr X n m := trivialInrHom_mul_trivialInrHom R N X n m
  smul_inr X b a n hb := by
    have hb' : sqZeroExtFst (M := modules N) b = a := hb
    refine (mul_trivialInrHom R N X b n).trans ?_
    exact congrArg (trivialInrHom R N X) (congrArg (fun r => r • n) hb')
  u := 𝟙 R
  v := sqZeroExtSheafInl R N
  base_comm := by
    rw [Category.comp_id, Category.id_comp]
    exact sqZeroExtSheafInl_comp_sqZeroExtSheafProj R N

/-- **The witness compatible morphism**: the zero section `R ⟶ R ⋉ 𝒢`. -/
def trivialCompatibleHom : (trivialData R N).CompatibleHom where
  hom := sqZeroExtSheafInl R N
  base_comm := Category.id_comp _
  proj_comm := by
    change sqZeroExtSheafInl R N ≫ sqZeroExtSheafProj R N
      = (𝟙 R : R ⟶ R) ≫ (𝟙 R : R ⟶ R)
    rw [Category.id_comp]
    exact sqZeroExtSheafInl_comp_sqZeroExtSheafProj R N
  kernel_comm X g := by
    have hg : (g : ↥(R.obj.obj X)) = 0 := g.2
    rw [hg]
    exact (map_zero _).trans (map_zero ((trivialData R N).inr X)).symm

omit [HasWeakSheafify K CommRingCat.{u}] [K.WEqualsLocallyBijective CommRingCat.{u}] in
/-- **The criterion of Stacks 0GQ2 is satisfiable**: for the witness setup a compatible
`S`-morphism exists. -/
theorem nonempty_compatibleHom_trivialData :
    Nonempty (trivialData R N).CompatibleHom := ⟨trivialCompatibleHom R N⟩

/-- **Both sides of the criterion hold for the witness setup**: `𝒪'₁` and `𝒪'₂` are isomorphic
extensions. -/
theorem isomorphic_trivialData :
    AlgebraExtension.Isomorphic (trivialData R N).pushoutExtension
      (trivialData R N).pullbackExtension :=
  ((trivialData R N).nonempty_compatibleHom_iff_isomorphic).1
    (nonempty_compatibleHom_trivialData R N)

end Witness

end Stacks.Deformation.InverseImageExtension

end
