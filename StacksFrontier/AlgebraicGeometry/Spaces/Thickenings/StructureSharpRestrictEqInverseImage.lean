module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AssociatedModulePullbackUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.LiftDifferenceDerivation
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentials
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.StructureSharpRestrictEq

/-!
# The two structure maps of two lifts, in inverse-image form

Let `G ⊂ X'` be a thickening of algebraic spaces over a scheme `S`, with inclusion
`i : X ⟶ X'`, and let `a', b' : X' ⟶ Y'` be two morphisms with `i ≫ a' = i ≫ b'`.
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.StructureSharpRestrictEq` proves that the two
structure maps `(a')^♯` and `(b')^♯`, put in parallel by the structure-sheaf half of
[Stacks Project, Tag 05ZM], become equal after the direct image along `b'` of
`i^♯ : 𝒪_{X'} ⟶ i_*𝒪_X`.  That is the *direct-image* form of the hypothesis `hfg` of
`AlgebraicGeometry.Space.liftDifference`.

This file transports it to the *inverse-image* form which `liftDifference` actually consumes:
two homomorphisms out of one and the same sheaf of rings on the small étale site of `X'` into
`𝒪_{X'}`.  The two homomorphisms are `(b')^♯ : (b')^{-1}𝒪_{Y'} ⟶ 𝒪_{X'}` and the structure map
of `a'` read on `(b')^{-1}𝒪_{Y'}` through a comparison
`(b')^{-1}𝒪_{Y'} ≅ (a')^{-1}𝒪_{Y'}` of the two inverse images.

With this the difference of the two structure maps of two lifts is formed, as
`AlgebraicGeometry.Space.liftPairDifference`, and the four equations which say that it is a
derivation — `AlgebraicGeometry.Space.liftDifference_add`,
`AlgebraicGeometry.Space.liftDifference_smul_add_smul`,
`AlgebraicGeometry.Space.liftDifference_app_eq_zero` and
`AlgebraicGeometry.Space.liftDifference_naturality` — apply to it verbatim.

## Main definitions

* `AlgebraicGeometry.Space.commRingInverseImageIsoOfRestrictEq`: the comparison
  `(a')^{-1} ≅ (b')^{-1}` of the two inverse images of sheaves of commutative rings.  It is the
  mate of the direct-image comparison
  `AlgebraicGeometry.Space.pushforwardCommRingFunctorIsoOfRestrictEq` of Tag 05ZM along
  `Stacks.Sheaves.ToposPushforward.commRingImageAdjunction`: uniqueness of left adjoints, the
  adjunction of `b'` being transported along that comparison.
* `AlgebraicGeometry.Space.inverseImageStructureSharpOfRestrictEq`: the structure map of `a'`
  in inverse-image form, read on `(b')^{-1}𝒪_{Y'}` through that comparison, so that it is
  parallel to `(b')^♯`.
* `AlgebraicGeometry.Space.liftPairDifference`: the difference of the two structure maps of two
  lifts, as a section of the defining ideal of the thickening.

## Main results

* `Stacks.CategoryTheory.eq_of_faithful_map_eq` and
  `Stacks.CategoryTheory.comp_natIso_inv_app_eq_of_transpose`: the two pieces of bookkeeping,
  with every datum a variable.
* `AlgebraicGeometry.RingedToposHom.homEquiv_fSharpInverseImage`: the transpose of the
  inverse-image form of a structure map is the structure map.
* `AlgebraicGeometry.Space.structureSharpCommRing_comp_pushforwardCommRingFunctorIsoOfRestrictEq`:
  the direct-image statement for sheaves of *commutative* rings.
* `AlgebraicGeometry.Space.inverseImageStructureSharpOfRestrictEq_comp_structureSharpCommRing`:
  the inverse-image statement.
* `AlgebraicGeometry.Space.inverseImageStructureSharpOfRestrictEq_comp_structureSharp`: the same
  for sheaves of rings, which is the hypothesis `hfg` of
  `AlgebraicGeometry.Space.liftDifference` at the pair of structure maps of two lifts.

## Implementation notes

**Why the comparison of the inverse images is a mate and not a construction.**  `(a')^{-1}` and
`(b')^{-1}` are both left adjoint to `(a')_*`, the second after transporting its adjunction
along the comparison of Tag 05ZM, so `CategoryTheory.Adjunction.leftAdjointUniq` compares them.
Its *values* are not computable — it is assembled from universal properties — but nothing here
needs them: what is needed is that it carries one named morphism to another, and that is a
statement about transposes, which is
`CategoryTheory.Adjunction.eq_leftAdjointUniq_hom_app_comp` together with
`CategoryTheory.Adjunction.homEquiv_naturality_right`.  The same construction at the level of
sheaves of sets is `AlgebraicGeometry.Space.smallEtaleInverseImageIsoOfRestrictEq`.

**Nothing is restated at the geometric instantiation.**  Both bookkeeping lemmas take every
datum as a variable — the two transposes, the comparison, the morphism being pushed forward and
the two presented composites — so each hypothesis at the instantiation is an existing lemma
applied verbatim: `AlgebraicGeometry.Space.map_structureSharpCommRing`,
`Stacks.Sheaves.ToposPullback.forgetCommRingSheaf_map_pullbackCommRingSheafMap`,
`AlgebraicGeometry.RingedToposHom.homEquiv_fSharpInverseImage` and the direct-image statement
itself.  In particular the naturality of the Tag 05ZM comparison at `i^♯`, which is what moves
the comparison from `𝒪_{X'}` to `i_*𝒪_X`, happens inside the generic lemma and not at the
instantiation.

**Why the commutative-ring statement is deduced from the ring one and not proved again.**  The
structure map of a morphism of algebraic spaces is defined on sheaves of rings
(`AlgebraicGeometry.Space.structureSharp`) and chosen on sheaves of commutative rings
(`AlgebraicGeometry.Space.structureSharpCommRing`), and forgetting commutativity is faithful on
sheaves.  So the commutative-ring statement follows from the ring-valued one of
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.StructureSharpRestrictEq` by faithfulness,
with the three identifications on underlying sheaves of rings supplied by existing lemmas; the
identification of the comparison of Tag 05ZM at the two levels is `rfl`, both being the same
transport of ring operations along one comparison of sheaves of sets.

Conversely the hypothesis which `AlgebraicGeometry.Space.liftDifference` consumes is at the
level of sheaves of *rings*, because the defining ideal of a closed subspace is carried on
`AlgebraicGeometry.Space.structureRingSheaf`.  The inverse-image statement is therefore proved
for sheaves of commutative rings — that is where the adjunction of
`AlgebraicGeometry.RingedToposHom.fSharpInverseImage` lives — and then carried down by applying
the forgetful functor to the whole equation, which needs nothing known about what it does to
the comparison.

## References

* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
* [Stacks Project, Tag 05ZM](https://stacks.math.columbia.edu/tag/05ZM)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 00YV](https://stacks.math.columbia.edu/tag/00YV)
-/

@[expose] public section

open CategoryTheory
open Stacks.Sheaves.ToposPullback
open Stacks.Sheaves.ToposPushforward

namespace Stacks.CategoryTheory

open _root_.CategoryTheory

universe v₁ u₁ v₂ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- **A three-factor equation checked after a faithful functor.**  For morphisms
`σ : O ⟶ P₁`, `Θ : P₁ ⟶ P₂`, `m : P₂ ⟶ Q` and `σ' : O ⟶ P₂`, the equation
`σ ≫ Θ ≫ m = σ' ≫ m` follows from the corresponding equation between the images of the four
morphisms under a functor `W` which is injective on the hom-set `O ⟶ Q`.

Each image is a *variable*, given by a hypothesis, so that at an instantiation no equation has
to be restated: the four hypotheses are existing lemmas applied verbatim. -/
theorem eq_of_faithful_map_eq (W : C ⥤ D) {O P₁ P₂ Q : C}
    (hinj : ∀ p q : O ⟶ Q, W.map p = W.map q → p = q)
    {σ : O ⟶ P₁} {Θ : P₁ ⟶ P₂} {m : P₂ ⟶ Q} {σ' : O ⟶ P₂}
    {σw : W.obj O ⟶ W.obj P₁} {Θw : W.obj P₁ ⟶ W.obj P₂} {mw : W.obj P₂ ⟶ W.obj Q}
    {σ'w : W.obj O ⟶ W.obj P₂}
    (hσ : W.map σ = σw) (hΘ : W.map Θ = Θw) (hm : W.map m = mw) (hσ' : W.map σ' = σ'w)
    (key : σw ≫ Θw ≫ mw = σ'w ≫ mw) :
    σ ≫ Θ ≫ m = σ' ≫ m := by
  refine hinj _ _ ?_
  rw [W.map_comp, W.map_comp, W.map_comp, hσ, hΘ, hm, hσ']
  exact key

/-- **An equation between two morphisms out of the two left adjoints of two comparable right
adjoints, transported along the comparison of the left adjoints.**  Let `adj1 : F ⊣ Gf` and
`adjb : F' ⊣ Gf'` be adjunctions and `E : Gf ≅ Gf'` a comparison of the two right adjoints, so
that `F` and `F'` are both left adjoint to `Gf` and
`CategoryTheory.Adjunction.leftAdjointUniq` compares them.  Given

* `s : F.obj x ⟶ c₀` and `s' : F'.obj x ⟶ c₀` with transposes `t` and `t'`,
* a morphism `m : c₀ ⟶ c`, and
* `t ≫ E.hom.app c₀ ≫ Gf'.map m = t' ≫ Gf'.map m`, the two transposes becoming equal after
  `Gf'.map m` when the first is read through `E`,

the comparison of the left adjoints carries `s' ≫ m` to `s ≫ m`.

Only naturality of `E` at `m` and the two transposes are used; the comparison of the left
adjoints is never computed.  Every datum is a variable, so that at an instantiation nothing is
restated. -/
theorem comp_natIso_inv_app_eq_of_transpose {F F' : C ⥤ D} {Gf Gf' : D ⥤ C}
    (adj1 : F ⊣ Gf) (adjb : F' ⊣ Gf') (E : Gf ≅ Gf') (x : C) {c₀ c : D}
    (s : F.obj x ⟶ c₀) (s' : F'.obj x ⟶ c₀) (m : c₀ ⟶ c)
    (t : x ⟶ Gf.obj c₀) (t' : x ⟶ Gf'.obj c₀)
    (ht : adj1.homEquiv x c₀ s = t) (ht' : adjb.homEquiv x c₀ s' = t')
    (key : t ≫ E.hom.app c₀ ≫ Gf'.map m = t' ≫ Gf'.map m) :
    (adj1.leftAdjointUniq (adjb.ofNatIsoRight E.symm)).inv.app x ≫ s ≫ m = s' ≫ m := by
  have hnat : t ≫ Gf.map m ≫ E.hom.app c = t' ≫ Gf'.map m := by
    rw [E.hom.naturality m]; exact key
  have hcomp : adj1.homEquiv x c (s ≫ m) =
      (adjb.ofNatIsoRight E.symm).homEquiv x c (s' ≫ m) := by
    rw [Adjunction.homEquiv_naturality_right, ht,
      Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_naturality_right, ht',
      Iso.symm_hom, ← hnat, Category.assoc, Category.assoc, Iso.hom_inv_id_app,
      Category.comp_id]
  rw [Adjunction.eq_leftAdjointUniq_hom_app_comp adj1 (adjb.ofNatIsoRight E.symm) x _ _ hcomp,
    ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

/-- **An equation precomposed with a morphism whose image is known is carried by a functor.**
From `p ≫ m = q ≫ m` and a description `W.map m = mw` of the image of `m`, the equation
`W.map p ≫ mw = W.map q ≫ mw` follows.  This is how an equation proved for sheaves of
commutative rings is read for sheaves of rings without knowing what the forgetful functor does
to anything but `m`. -/
theorem map_comp_eq_of_eq (W : C ⥤ D) {A P Q : C} {p q : A ⟶ P} {m : P ⟶ Q}
    {mw : W.obj P ⟶ W.obj Q} (hm : W.map m = mw) (e : p ≫ m = q ≫ m) :
    W.map p ≫ mw = W.map q ≫ mw := by
  rw [← hm, ← W.map_comp, ← W.map_comp, e]

end Stacks.CategoryTheory

namespace AlgebraicGeometry.RingedToposHom

open Stacks.Sheaves.LocallyRingedTopos

universe v₁ u₁ w₁ v₂ u₂ w₂

variable {X : RingedTopos.{v₁, u₁, w₁}} {Y : RingedTopos.{v₂, u₂, w₂}}
  [X.J.HasSheafCompose (forget RingCat.{w₁})]
  [Y.J.HasSheafCompose (forget RingCat.{w₂})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w₂} RingCat.{w₂})]

/-- **The transpose of the inverse-image form of a structure map is the structure map.**
`AlgebraicGeometry.RingedToposHom.fSharpInverseImage` is by definition the adjunct of `fSharp`
along `Stacks.Sheaves.ToposPushforward.commRingImageAdjunction`, so transposing it back returns
`fSharp`.  This is the only property of it any of this file uses. -/
theorem homEquiv_fSharpInverseImage (f : RingedToposHom X Y) :
    (commRingImageAdjunction f.toToposHom).homEquiv Y.O X.O f.fSharpInverseImage = f.fSharp :=
  Equiv.apply_symm_apply _ _

end AlgebraicGeometry.RingedToposHom

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The direct image of the structure map of a closed immersion, for commutative rings -/

section Push

variable {X Y Z : AlgebraicSpaces B S hS}

/-- **On underlying sheaves of rings, the direct image of the structure map of `k` along `f`
for sheaves of commutative rings is the direct image of the structure map of `k` for sheaves of
rings.**  Both are the transport of the ring operations along the same functor of sheaves of
sets. -/
theorem forget₂_pushforwardCommRingFunctor_map_structureSharpCommRing (f : X ⟶ Y) (k : Z ⟶ X) :
    (sheafCompose (SmallEtale.topology B S hS Y.1)
          (forget₂ CommRingCat.{u} RingCat.{u})).map
        ((pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
            (smallToposMorphismTypeU B S hS f)).map
          (structureSharpCommRing B S hS k)) =
      pullbackRingSheafMap.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS Y.1)
        (smallEtaleDirectImage B S hS f) (structureSharp B S hS k) :=
  (forgetCommRingSheaf_map_pullbackCommRingSheafMap.{u, u, u, u + 1, u, u + 1}
      (SmallEtale.topology B S hS Y.1) (smallToposMorphismTypeU B S hS f).pushforward
      (structureSharpCommRing B S hS k)).trans
    (congrArg (fun m ↦ pullbackRingSheafMap.{u, u, u, u + 1, u, u + 1}
      (SmallEtale.topology B S hS Y.1) (smallEtaleDirectImage B S hS f) m)
      (map_structureSharpCommRing B S hS k))

end Push

/-! ### Two morphisms agreeing on the closed subspace -/

section Restrict

variable {X' Y' : AlgebraicSpaces B S hS} {G : Subfunctor X'.1}
  (hG : IsThickening B S hS X' G) (a' b' : X' ⟶ Y')
  (h : IsThickening.inclusion B S hS hG ≫ a' = IsThickening.inclusion B S hS hG ≫ b')

/-- **On underlying sheaves of rings the comparison of Tag 05ZM for sheaves of commutative
rings is the comparison for sheaves of rings.**  Both
`AlgebraicGeometry.Space.pushforwardCommRingFunctorIsoOfRestrictEq` and
`AlgebraicGeometry.Space.structureRingSheafDirectImageIsoOfRestrictEq` are the transport of the
ring operations of `𝒪_{X'}` along `AlgebraicGeometry.Space.smallEtalePushforwardIsoOfRestrictEq`,
so forgetting commutativity in the first gives the second. -/
theorem forget₂_pushforwardCommRingFunctorIsoOfRestrictEq :
    (sheafCompose (SmallEtale.topology B S hS Y'.1)
          (forget₂ CommRingCat.{u} RingCat.{u})).map
        ((pushforwardCommRingFunctorIsoOfRestrictEq B S hS hG a' b' h).hom.app
          (smallEtaleRingedTopos B S hS X').O) =
      (structureRingSheafDirectImageIsoOfRestrictEq B S hS hG a' b' h).hom :=
  rfl

/-- **The two structure maps of two lifts agree after the structure map of the thickening**, for
sheaves of *commutative* rings.  This is
`AlgebraicGeometry.Space.structureSharpOfRestrictEq_comp_pushforward_structureSharp` at the
level where the adjunction between the inverse image and the direct image of a structure map
lives, obtained from it by faithfulness of forgetting commutativity. -/
theorem structureSharpCommRing_comp_pushforwardCommRingFunctorIsoOfRestrictEq :
    structureSharpCommRing B S hS a' ≫
        (pushforwardCommRingFunctorIsoOfRestrictEq B S hS hG a' b' h).hom.app
          (smallEtaleRingedTopos B S hS X').O ≫
        (pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
            (smallToposMorphismTypeU B S hS b')).map
          (structureSharpCommRing B S hS (IsThickening.inclusion B S hS hG)) =
      structureSharpCommRing B S hS b' ≫
        (pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
            (smallToposMorphismTypeU B S hS b')).map
          (structureSharpCommRing B S hS (IsThickening.inclusion B S hS hG)) :=
  Stacks.CategoryTheory.eq_of_faithful_map_eq
    (sheafCompose (SmallEtale.topology B S hS Y'.1) (forget₂ CommRingCat.{u} RingCat.{u}))
    (fun _ _ ↦ (fullyFaithfulForgetCommRingSheaf.{u, u, u + 1}
      (SmallEtale.topology B S hS Y'.1)).map_injective)
    (map_structureSharpCommRing B S hS a')
    (forget₂_pushforwardCommRingFunctorIsoOfRestrictEq B S hS hG a' b' h)
    (forget₂_pushforwardCommRingFunctor_map_structureSharpCommRing B S hS b'
      (IsThickening.inclusion B S hS hG))
    (map_structureSharpCommRing B S hS b')
    ((Category.assoc _ _ _).symm.trans
      (structureSharpOfRestrictEq_comp_pushforward_structureSharp B S hS hG a' b' h))

/-- **The comparison of the two inverse images of sheaves of commutative rings.**  For a
thickening `G ⊂ X'` with inclusion `i : X ⟶ X'` and two morphisms `a', b' : X' ⟶ Y'` with
`i ≫ a' = i ≫ b'`, the two inverse images `(a')^{-1}` and `(b')^{-1}` of sheaves of commutative
rings on the small étale sites are isomorphic functors.

This is the mate of the direct-image comparison
`AlgebraicGeometry.Space.pushforwardCommRingFunctorIsoOfRestrictEq` of Tag 05ZM: both
`(a')^{-1}` and `(b')^{-1}` are left adjoint to `(a')_*`, the second after transporting its
adjunction along that comparison, so uniqueness of left adjoints compares them.  The same
construction for sheaves of sets is
`AlgebraicGeometry.Space.smallEtaleInverseImageIsoOfRestrictEq`. -/
noncomputable def commRingInverseImageIsoOfRestrictEq :
    inverseImageCommRingFunctor.{u, u, u, u + 1, u, u + 1}
        (smallToposMorphismTypeU B S hS a') ≅
      inverseImageCommRingFunctor.{u, u, u, u + 1, u, u + 1}
        (smallToposMorphismTypeU B S hS b') :=
  Adjunction.leftAdjointUniq
    (commRingImageAdjunction.{u, u, u, u + 1, u, u + 1} (smallToposMorphismTypeU B S hS a'))
    ((commRingImageAdjunction.{u, u, u, u + 1, u, u + 1}
        (smallToposMorphismTypeU B S hS b')).ofNatIsoRight
      (pushforwardCommRingFunctorIsoOfRestrictEq B S hS hG a' b' h).symm)

/-- **The structure map of `a'` in inverse-image form, read on `(b')^{-1}𝒪_{Y'}`.**  Through
`AlgebraicGeometry.Space.commRingInverseImageIsoOfRestrictEq` the inverse-image form
`(a')^♯ : (a')^{-1}𝒪_{Y'} ⟶ 𝒪_{X'}` of the structure map of `a'` becomes a homomorphism
`(b')^{-1}𝒪_{Y'} ⟶ 𝒪_{X'}`, parallel to `(b')^♯` itself.

This pair of parallel homomorphisms *into* `𝒪_{X'}` is the shape which
`AlgebraicGeometry.Space.liftDifference` consumes, and which
`AlgebraicGeometry.Space.structureSharpOfRestrictEq` — the same pair in direct-image form — is
not. -/
noncomputable def inverseImageStructureSharpOfRestrictEq :
    inverseImageStructureSheaf B S hS b' ⟶ (smallEtaleRingedTopos B S hS X').O :=
  (commRingInverseImageIsoOfRestrictEq B S hS hG a' b' h).inv.app
      (smallEtaleRingedTopos B S hS Y').O ≫
    structureSharpInverseImage B S hS a'

/-- **The two structure maps of two lifts, in inverse-image form, agree after the structure map
of the thickening.**  For sheaves of commutative rings: the structure map of `a'` read on
`(b')^{-1}𝒪_{Y'}` and the structure map of `b'` become equal after
`i^♯ : 𝒪_{X'} ⟶ i_*𝒪_X`.

Both are morphisms out of the inverse image, hence determined by their transposes, and those
transposes are the two sides of
`AlgebraicGeometry.Space.structureSharpCommRing_comp_pushforwardCommRingFunctorIsoOfRestrictEq`.
The comparison of the two inverse images is never computed. -/
theorem inverseImageStructureSharpOfRestrictEq_comp_structureSharpCommRing :
    inverseImageStructureSharpOfRestrictEq B S hS hG a' b' h ≫
        structureSharpCommRing B S hS (IsThickening.inclusion B S hS hG) =
      structureSharpInverseImage B S hS b' ≫
        structureSharpCommRing B S hS (IsThickening.inclusion B S hS hG) :=
  (Category.assoc _ _ _).trans
    (Stacks.CategoryTheory.comp_natIso_inv_app_eq_of_transpose
      (commRingImageAdjunction.{u, u, u, u + 1, u, u + 1} (smallToposMorphismTypeU B S hS a'))
      (commRingImageAdjunction.{u, u, u, u + 1, u, u + 1} (smallToposMorphismTypeU B S hS b'))
      (pushforwardCommRingFunctorIsoOfRestrictEq B S hS hG a' b' h)
      (smallEtaleRingedTopos B S hS Y').O
      (structureSharpInverseImage B S hS a') (structureSharpInverseImage B S hS b')
      (structureSharpCommRing B S hS (IsThickening.inclusion B S hS hG))
      (structureSharpCommRing B S hS a') (structureSharpCommRing B S hS b')
      (RingedToposHom.homEquiv_fSharpInverseImage (smallEtaleRingedToposHom B S hS a'))
      (RingedToposHom.homEquiv_fSharpInverseImage (smallEtaleRingedToposHom B S hS b'))
      (structureSharpCommRing_comp_pushforwardCommRingFunctorIsoOfRestrictEq
        B S hS hG a' b' h))

/-- **The hypothesis `hfg` of `AlgebraicGeometry.Space.liftDifference` at the pair of structure
maps of two lifts.**  The same statement as
`AlgebraicGeometry.Space.inverseImageStructureSharpOfRestrictEq_comp_structureSharpCommRing`,
read for sheaves of rings, which is the level at which the defining ideal of the thickening
lives.

The forgetful functor is applied to the whole equation, so nothing has to be known about what it
does to the comparison of the two inverse images — only about the structure map of the
inclusion, which is `AlgebraicGeometry.Space.map_structureSharpCommRing`. -/
@[stacks 0618 "the two structure maps of two lifts, as a pair of parallel homomorphisms into \
the structure sheaf of the thickening which agree after the structure map of the inclusion"]
theorem inverseImageStructureSharpOfRestrictEq_comp_structureSharp :
    (sheafCompose (SmallEtale.topology B S hS X'.1)
            (forget₂ CommRingCat.{u} RingCat.{u})).map
          (inverseImageStructureSharpOfRestrictEq B S hS hG a' b' h) ≫
        structureSharp B S hS (subspaceInclusion B S hS X' ⟨G, hG.1⟩) =
      (sheafCompose (SmallEtale.topology B S hS X'.1)
            (forget₂ CommRingCat.{u} RingCat.{u})).map
          (structureSharpInverseImage B S hS b') ≫
        structureSharp B S hS (subspaceInclusion B S hS X' ⟨G, hG.1⟩) :=
  Stacks.CategoryTheory.map_comp_eq_of_eq _
    (map_structureSharpCommRing B S hS (IsThickening.inclusion B S hS hG))
    (inverseImageStructureSharpOfRestrictEq_comp_structureSharpCommRing B S hS hG a' b' h)

/-- **The difference of the two structure maps of two lifts**, as a section of the defining
ideal of the thickening.  This is the derivation `D` of [Stacks Project, Tag 0618] for two
morphisms `a', b' : X' ⟶ Y'` of a thickening `G ⊂ X'` which agree on its closed subspace: it is
`AlgebraicGeometry.Space.liftDifference` applied to the pair of parallel homomorphisms
`(a')^♯, (b')^♯ : (b')^{-1}𝒪_{Y'} ⟶ 𝒪_{X'}`.

Its four defining equations are `AlgebraicGeometry.Space.liftDifference_add`,
`AlgebraicGeometry.Space.liftDifference_smul_add_smul`,
`AlgebraicGeometry.Space.liftDifference_app_eq_zero` and
`AlgebraicGeometry.Space.liftDifference_naturality`, which apply to it verbatim. -/
@[stacks 0618 "the derivation, for the two structure maps of two morphisms of a thickening \
agreeing on its closed subspace"]
noncomputable def liftPairDifference (U : (SmallEtale B S hS X'.1)ᵒᵖ)
    (r : ((sheafCompose (SmallEtale.topology B S hS X'.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (inverseImageStructureSheaf B S hS b')).obj.obj U) :
    definingIdealAt B S hS X' ⟨G, hG.1⟩ U :=
  liftDifference B S hS ⟨G, hG.1⟩
    ((sheafCompose (SmallEtale.topology B S hS X'.1)
        (forget₂ CommRingCat.{u} RingCat.{u})).map
      (inverseImageStructureSharpOfRestrictEq B S hS hG a' b' h))
    ((sheafCompose (SmallEtale.topology B S hS X'.1)
        (forget₂ CommRingCat.{u} RingCat.{u})).map
      (structureSharpInverseImage B S hS b'))
    (inverseImageStructureSharpOfRestrictEq_comp_structureSharp B S hS hG a' b' h) U r

end Restrict

end AlgebraicGeometry.Space

end
