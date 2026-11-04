module

public import StacksFrontier.AlgebraicGeometry.AlgebraPullbackQcoh.MateStalk
public import StacksFrontier.AlgebraicGeometry.AlgebraPullbackQcoh.UnitStalk
public import StacksFrontier.AlgebraicGeometry.PullbackTensorIso.Invertible

/-!
# The stalk of the pullback algebra as a tensor product over the stalks of the base

Let `g : T ⟶ S` be a morphism of schemes, `A` a sheaf of commutative `𝒪_S`-algebras and
`t : T`.  `Stacks.AffineAlgebraEquivalence.stalkAlgebraPullbackIso` computes the stalk at `t`
of `Stacks.AffineAlgebraEquivalence.algebraPullback g` of `A` as the tensor product
`(g⁻¹A)_t ⊗_{(g⁻¹𝒪_S)_t} 𝒪_{T,t}` — a tensor product over the stalks of *inverse-image*
sheaves, which is not the shape the stalk of a module pullback is computed in.

**This file rewrites it as `𝒪_{T,t} ⊗_{𝒪_{S,g t}} A_{g t}`**, a tensor product over the
stalks of `S` and of `A` at `g t`, with the base ring acting through the stalk map of `g`.  It
also gives that identification on the elements the quasi-coherence clause of
[Stacks, Tag 01SA] needs, namely `1 ⊗ germ a`.

## Main definitions

* `Stacks.AlgebraPullbackQcoh.mateStalkIso`: the inverse-image stalk comparison
  `F_{g t} ≅ (g⁻¹F)_t` of `Stacks.SkyscraperPushforward.stalkSheafPullbackMateNatIso`, at a
  single sheaf of commutative rings.
* `Stacks.AlgebraPullbackQcoh.ringedSpaceHom`: `g` read as a morphism of ringed spaces.
* `Stacks.AlgebraPullbackQcoh.schemeStalkAlgebra`: the `𝒪_{S,g t}`-algebra structure on
  `𝒪_{T,t}`, taken in the spelling `Stacks.PullbackTensorIso.commStalkAlgebra` provides so
  that the source and the target of the comparison are tensor products over the *same*
  algebra instance.
* `Stacks.AlgebraPullbackQcoh.targetStalkIso` and `targetStalkLinearEquiv`: **the
  identification**, as an isomorphism of commutative rings and as an `𝒪_{T,t}`-linear
  equivalence.

## Main results

* `Stacks.AlgebraPullbackQcoh.ofHom_commStalkRingMap`: the stalk map of `g` between the
  `CommRingCat` stalks of the structure sheaves, obtained by conjugating the `RingCat` stalk
  map with `Stacks.PullbackTensorIso.stalkRingEquiv`, is Mathlib's
  `AlgebraicGeometry.Scheme.Hom.stalkMap`.
* `Stacks.AlgebraPullbackQcoh.isPushout_stalk_target`: **the transported pushout square.**
  The stalk of the square exhibiting `algebraPullback` as an extension of scalars, with its
  two inverse-image corners replaced by `𝒪_{S,g t}` and `A_{g t}`, is again a pushout.
* `Stacks.AlgebraPullbackQcoh.targetStalkIso_includeLeft`: the `𝒪_{T,t}`-leg of the tensor
  product is the stalk of the structure morphism of the pullback algebra.
* `Stacks.AlgebraPullbackQcoh.targetStalkIso_hom_one_tmul_germ`: **the identification on
  elements.**  It carries `1 ⊗ germ a` to the germ of the image of the inverse-image-unit
  image of `a` under `Stacks.AffineAlgebraEquivalence.algebraPullbackMap`.

## Route

`CategoryTheory.IsPushout.of_iso'` transports
`Stacks.AffineAlgebraEquivalence.isPushout_stalk_algebraPullback` along two instances of
`mateStalkIso`.  Its two compatibility conditions are exactly two statements of the library: on the
top edge, naturality of `Stacks.SkyscraperPushforward.stalkSheafPullbackMateNatIso` in the
sheaf, applied to the structure morphism of `A`; on the left edge,
`Stacks.AlgebraPullbackQcoh.stalkInverseImageMate_inverseImageStructureMap`, which says that
under the comparison the stalk of `g⁻¹𝒪_S ⟶ 𝒪_T` is the stalk map of `g`.
`CommRingCat.isPushout_tensorProduct` together with
`CategoryTheory.IsPushout.isoIsPushout` then turns the transported square into a tensor
product, and the two leg identities of `isoIsPushout` give the element formulas.

The square is flipped before the tensor product is taken, so that the base ring is the first
factor and the stalk of `A` the second.  That is the order the stalk of a module pullback
comes in, and it is what lets the two sides be compared with no commutativity isomorphism.

## Why `commStalkRingMap` and not `stalkMap`

The source side of the quasi-coherence clause is
`Stacks.PullbackTensorIso.pullbackStalkEquiv`, whose tensor product is taken over the
`Algebra` instance `Stacks.PullbackTensorIso.commStalkAlgebra`, built from
`commStalkRingMap`.  A tensor product taken over a different `Algebra` instance with the same
underlying ring map is a different type, so the target side is stated over the same instance;
`ofHom_commStalkRingMap` is what makes the pushout square available there.

## What is not done

**No clause of [Stacks, Tag 01SA] is proved here, and no project tag attribute is attached.**
The statement of Tag 01SA carries a single unqualified tag on a nine-field structure.  This
file is one input to the `algebraPullback_isQuasicoherent` clause, which is discharged in the
sibling `StacksFrontier/AlgebraicGeometry/AlgebraPullbackQcoh/Invertible.lean`; the tag's
base-change isomorphism and the identification of that isomorphism are open and are not
touched here.

No quasi-coherence, affineness, Noetherian, finiteness or flatness hypothesis occurs in this
file: `g`, `A` and `t` are arbitrary.

## Transparency gotchas

* `Stacks.PullbackTensorIso.commStalkAlgebra (ringedSpaceHom g) t` has its base ring spelled
  `Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk S.toRingedSpace ((ringedSpaceHom
    g).hom.base t)`, which is the same
  point as `g.base t` only after unfolding.  Instance search is syntactic, so the instance is
  not found at the scheme spelling; `schemeStalkAlgebra` re-types it with `g.base t`, after
  which both spellings of the tensor product are available and are interchangeable by `exact`.
* `isPushout_stalk_target` is proved by giving the transport its compatibility proofs
  directly, not by rewriting with `ofHom_commStalkRingMap` first: the rewrite fails to build a
  motive, the two sides of that equation being definitionally equal morphisms whose domains
  are two spellings of one stalk.
* The `𝒪_{T,t}`-linearity of `targetStalkIso` is multiplicativity of the underlying ring
  isomorphism, but `map_mul` has to be restated at the `RingEquiv.toAddEquiv` spelling the
  goal carries, since `AddEquiv.toLinearEquiv` presents the map as an additive equivalence and
  no `MulHomClass` instance is found for it.

## References

* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat
open scoped TensorProduct

universe u

namespace Stacks.AlgebraPullbackQcoh

open Stacks.AffineAlgebraEquivalence Stacks.RelativeSpec Stacks.PullbackTensorIso

variable {T S : Scheme.{u}} (g : T ⟶ S) (A : AlgebraSheaf S) (t : T)

/-- **The inverse-image stalk comparison at a single sheaf**, `F_{g t} ≅ (g⁻¹F)_t`.  This is
`Stacks.SkyscraperPushforward.stalkSheafPullbackMateNatIso` read at a component; its effect on
germs is `Stacks.AlgebraPullbackQcoh.germ_stalkSheafPullbackMateNatIso`. -/
abbrev mateStalkIso (F : TopCat.Sheaf CommRingCat.{u} S.toTopCat) :
    (stalkOnSheaf (T := S) (g.base t)).obj F ≅
      (stalkOnSheaf (T := T) t).obj ((TopCat.Sheaf.pullback CommRingCat.{u} g.base).obj F) :=
  (Stacks.SkyscraperPushforward.stalkSheafPullbackMateNatIso CommRingCat.{u} g.base t).app F

/-- A morphism of schemes read as a morphism of the underlying ringed spaces.  Every
ringed-space construction used below transfers to a scheme morphism along this with no
bridge: the ring sheaf, the structure-sheaf morphism, the stalk ring map and the module
pullback of the ringed space are the scheme-level ones by `rfl`. -/
abbrev ringedSpaceHom : T.toRingedSpace ⟶ S.toRingedSpace := g.toLRSHom.toShHom

/-- **The two stalk maps of `g` between the `CommRingCat` stalks of the structure sheaves
agree.**  `Stacks.PullbackTensorIso.commStalkRingMap`, obtained by conjugating the `RingCat`
stalk map of the ringed-space morphism with the two comparisons
`Stacks.PullbackTensorIso.stalkRingEquiv`, is Mathlib's
`AlgebraicGeometry.Scheme.Hom.stalkMap`.  Both carry the germ of a section `r` to the germ of
`g.c r`. -/
lemma ofHom_commStalkRingMap :
    CommRingCat.ofHom (commStalkRingMap (ringedSpaceHom g) t) = g.stalkMap t := by
  refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
  obtain ⟨V, hV, r₀, hr⟩ := TopCat.Presheaf.exists_germ_eq S.toRingedSpace.presheaf r
  have hL : commStalkRingMap (ringedSpaceHom g) t
        (TopCat.Presheaf.germ S.toRingedSpace.presheaf V (g.base t) hV r₀) =
      TopCat.Presheaf.germ T.toRingedSpace.presheaf ((Opens.map g.base).obj V) t hV
        (g.c.app (op V) r₀) := by
    refine (congrArg (stalkRingEquiv T.toRingedSpace t).symm
      ((congrArg (Stacks.ModuleSkyscraper.ringedSpaceStalkRingMap (ringedSpaceHom g) t).hom
          (stalkRingEquiv_germ S.toRingedSpace (g.base t) V hV r₀)).trans
        (Stacks.ModuleSkyscraper.stalkRingMap_germ g.base
          (structureSheafRing T.toRingedSpace)
          (structureSheafRing S.toRingedSpace)
          (RingedSpaceModuleAdjunction.structureSheafHom (ringedSpaceHom g)) t V hV r₀))).trans ?_
    exact (stalkRingEquiv T.toRingedSpace t).symm_apply_eq.2
      (stalkRingEquiv_germ T.toRingedSpace t ((Opens.map g.base).obj V) hV
        (g.c.app (op V) r₀)).symm
  rw [← hr]
  exact hL.trans (g.germ_stalkMap_apply V t hV r₀).symm

/-- The `𝒪_{S,g t}`-algebra structure on `𝒪_{T,t}` given by the stalk map of `g`, re-typed so
that the point of `S` is spelled `g.base t`.  See the transparency notes: without this,
instance search does not find the algebra structure at the scheme spelling. -/
abbrev schemeStalkAlgebra : Algebra (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk
  S.toRingedSpace (g.base t))
    (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk T.toRingedSpace t) :=
  commStalkAlgebra (ringedSpaceHom g) t

attribute [local instance] algebraStalkAlgebra schemeStalkAlgebra

/-- **The stalk of the extension-of-scalars square, over the stalks of the base.**  The stalk
at `t` of the square exhibiting `Stacks.AffineAlgebraEquivalence.algebraPullback` as an
extension of scalars is a pushout square of commutative rings; transporting its two
inverse-image corners along `mateStalkIso` turns it into the square with corners `𝒪_{S,g t}`,
`A_{g t}`, `𝒪_{T,t}` and the stalk of the pullback algebra, whose two edges out of `𝒪_{S,g t}`
are the stalk of the structure morphism of `A` and the stalk map of `g`. -/
theorem isPushout_stalk_target :
    IsPushout (algebraStalkMap A (g.base t))
      (CommRingCat.ofHom (commStalkRingMap (ringedSpaceHom g) t))
      ((mateStalkIso g t A.right).hom ≫ (stalkOnSheaf t).map ((algebraPullbackMap g).app A))
      ((stalkOnSheaf t).map ((algebraPullback g).obj A).hom) :=
  (isPushout_stalk_algebraPullback g A t).of_iso' (mateStalkIso g t S.sheaf)
    (mateStalkIso g t A.right) (Iso.refl _) (Iso.refl _)
    ((Stacks.SkyscraperPushforward.stalkSheafPullbackMateNatIso CommRingCat.{u}
      g.base t).hom.naturality A.hom).symm
    ((stalkInverseImageMate_inverseImageStructureMap g t).trans
      ((ofHom_commStalkRingMap g t).symm.trans (Category.comp_id _).symm))
    (Category.comp_id _).symm ((Category.id_comp _).trans (Category.comp_id _).symm)

/-- **The stalk of the pullback algebra is `𝒪_{T,t} ⊗_{𝒪_{S,g t}} A_{g t}`.**  The flipped
pushout square of `isPushout_stalk_target` and the tensor-product pushout square of
`CommRingCat.isPushout_tensorProduct` have the same two edges out of `𝒪_{S,g t}`, so their
pushouts are canonically isomorphic. -/
def targetStalkIso :
    CommRingCat.of (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk T.toRingedSpace t ⊗[
        Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk S.toRingedSpace (g.base t)]
          algebraStalk A (g.base t)) ≅
      (stalkOnSheaf t).obj ((algebraPullback g).obj A).right :=
  (CommRingCat.isPushout_tensorProduct _ _ _).isoIsPushout _ _
    (isPushout_stalk_target g A t).flip

/-- **The `𝒪_{T,t}`-leg.**  Under the identification, the inclusion of the first tensor factor
is the stalk of the structure morphism of the pullback algebra.  This is what makes the
identification `𝒪_{T,t}`-linear. -/
lemma targetStalkIso_includeLeft :
    CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk S.toRingedSpace (g.base t))
        (A := Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk T.toRingedSpace t)
        (B := algebraStalk A (g.base t))) ≫ (targetStalkIso g A t).hom =
      algebraStalkMap ((algebraPullback g).obj A) t :=
  (CommRingCat.isPushout_tensorProduct (ToType
    (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk S.toRingedSpace
      (g.base t))) (ToType (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk T.toRingedSpace
        t))
      (ToType (algebraStalk A (g.base t)))).inl_isoIsPushout_hom _ _
    (isPushout_stalk_target g A t).flip

/-- **The identification on elements.**  It carries `1 ⊗ germ a`, for `a` a section of `A`
over an open `V` containing `g t`, to the germ at `t` of the image under
`Stacks.AffineAlgebraEquivalence.algebraPullbackMap` of the inverse-image-unit image of `a`.

This is the `A_{g t}`-leg of the tensor product, followed by the germ formula for the
inverse-image stalk comparison and by the effect of the stalk functor on germs. -/
lemma targetStalkIso_hom_one_tmul_germ (V : S.Opens) (hV : g.base t ∈ V)
    (a : A.right.obj.obj (op V)) :
    (targetStalkIso g A t).hom.hom
        ((1 : Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk T.toRingedSpace t) ⊗ₜ
          TopCat.Presheaf.germ A.right.obj V (g.base t) hV a) =
      TopCat.Presheaf.germ ((algebraPullback g).obj A).right.obj
        ((Opens.map g.base).obj V) t hV
        (((algebraPullbackMap g).app A).hom.app (op ((Opens.map g.base).obj V))
          (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g.base).unit.app
            A.right).hom.app (op V) a)) := by
  have h1 := ConcreteCategory.congr_hom
    ((CommRingCat.isPushout_tensorProduct
        (ToType (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk S.toRingedSpace (g.base t)))
        (ToType (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk T.toRingedSpace t))
        (ToType (algebraStalk A (g.base t)))).inr_isoIsPushout_hom _ _
      (isPushout_stalk_target g A t).flip)
    (TopCat.Presheaf.germ A.right.obj V (g.base t) hV a)
  have h2 := ConcreteCategory.congr_hom
    (Stacks.AlgebraPullbackQcoh.germ_stalkSheafPullbackMateNatIso CommRingCat.{u} g.base t
      A.right V hV) a
  have h3 := TopCat.Presheaf.stalkFunctor_map_germ_apply ((Opens.map g.base).obj V) t hV
    ((algebraPullbackMap g).app A).hom
    (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g.base).unit.app
      A.right).hom.app (op V) a)
  exact h1.trans
    ((congrArg (((stalkOnSheaf t).map ((algebraPullbackMap g).app A)).hom) h2).trans h3)

/-- **The identification as an `𝒪_{T,t}`-linear equivalence.**  The underlying ring
isomorphism carries the first tensor factor to the stalk of the structure morphism of the
pullback algebra by `targetStalkIso_includeLeft`, so it is linear for the two module
structures those two ring maps define. -/
def targetStalkLinearEquiv :
    (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk T.toRingedSpace t ⊗[
        Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk S.toRingedSpace (g.base t)]
          algebraStalk A (g.base t))
      ≃ₗ[Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk T.toRingedSpace t]
      algebraStalk ((algebraPullback g).obj A) t := by
  refine AddEquiv.toLinearEquiv
    (CategoryTheory.Iso.commRingCatIsoToRingEquiv (targetStalkIso g A t)).toAddEquiv ?_
  intro r z
  have h := ConcreteCategory.congr_hom (targetStalkIso_includeLeft g A t) r
  have hm : ∀ x y, (CategoryTheory.Iso.commRingCatIsoToRingEquiv
          (targetStalkIso g A t)).toAddEquiv (x * y) =
        (CategoryTheory.Iso.commRingCatIsoToRingEquiv (targetStalkIso g A t)).toAddEquiv x *
          (CategoryTheory.Iso.commRingCatIsoToRingEquiv (targetStalkIso g A t)).toAddEquiv y :=
    fun x y => (CategoryTheory.Iso.commRingCatIsoToRingEquiv (targetStalkIso g A t)).map_mul x y
  rw [Algebra.smul_def, Algebra.smul_def, hm]
  exact congrArg (fun y => y * (CategoryTheory.Iso.commRingCatIsoToRingEquiv
    (targetStalkIso g A t)).toAddEquiv z) h

end Stacks.AlgebraPullbackQcoh

end
