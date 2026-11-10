module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonBraided
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleTwistSuccessor

/-!
# The braiding and the inverse-image comparison, at the scheme spelling

The induction step of [Stacks, Tag 0F27] has to compare the two orders `(F ⊗ L) ⊗ L^{⊗ n}` and
`(F ⊗ L^{⊗ n}) ⊗ L` of a double twist: the cokernel of multiplication by a section comes out in
the first order, while `Stacks.Algebraization.CoherentTriple.twistZ` is written in the second.
Between the two sit an associativity constraint, a braiding whiskered into `F`, and an
associativity constraint back, and for those to assemble into a morphism of *coherent triples*
rather than a pair of unrelated isomorphisms of modules, each needs its compatibility square
with the inverse-image comparison of [Stacks, Tag 01CD].

The associator's square is `Stacks.Algebraization.pullbackTensorModulesIso_associator`. This
file supplies the braiding's, which was the one piece of that raw material with no statement at
the scheme spelling, pastes the three into the reordering square, and assembles the reordering of
a double twist as a morphism of coherent triples.

## Main definitions

* `Stacks.Algebraization.strictModulesBraided`: the braided companion of
  `Stacks.Algebraization.strictModulesMonoidal` -- the symmetry constraint of
  [Stacks, Tag 01CA] on the `𝒪_X`-modules of a scheme, in the spelling whose tensor product is
  `Stacks.RelativeVeryAmple.tensorModules` on the nose.
* `Stacks.Algebraization.CoherentTriple.twistZTensorInvertibleBraidHom`: **the reordering of a
  double twist, as a morphism of coherent triples**
  `(T ⊗ L^{⊗ n}) ⊗ Q ⟶ (T ⊗ Q) ⊗ L^{⊗ n}`.
* `Stacks.Algebraization.CoherentTriple.tensorInvertibleTwistZSuccDegreeOneHom`: its composite
  with the successor identification -- **the twist by `L^{⊗ n}` of a tensor product with `L` is
  the `(n + 1)`-st twist**, `(T ⊗ L) ⊗ L^{⊗ n} ⟶ T ⊗ L^{⊗ (n + 1)}`, which is the
  identification the induction step of [Stacks, Tag 0F27] needs for the middle term of its short
  exact sequence.

## Main results

* `Stacks.Algebraization.pullbackTensorModulesIso_braiding`: **[Stacks, Tag 01CD] is compatible
  with the symmetry constraint of [Stacks, Tag 01CA]**, at the scheme spelling.
* `Stacks.Algebraization.pullbackTensorModulesIso_braid`: **[Stacks, Tag 01CD] carries the
  reordering of a double tensor product to the reordering** -- the three squares pasted.
* `Stacks.Algebraization.assoc_braid_assoc_naturality`: **the reordering of a double tensor
  product is natural in all three factors**, in an abstract braided monoidal category.
* `Stacks.Algebraization.alpha_twistZ_tensorInvertible_braid`: **the reordering of a double twist
  carries the identification of `(T ⊗ L^{⊗ n}) ⊗ Q` to the identification of
  `(T ⊗ Q) ⊗ L^{⊗ n}`** -- the compatibility square of the morphism of triples.
* `Stacks.Algebraization.CoherentTriple.isIso_twistZTensorInvertibleBraidHom` and
  `Stacks.Algebraization.CoherentTriple.isIso_tensorInvertibleTwistZSuccDegreeOneHom`: both
  members of each of the two morphisms above are isomorphisms, which is the form in which
  `Stacks.Algebraization.CoherentTriple.ShortExact.compIso` and
  `Stacks.Algebraization.CoherentTriple.eulerCharacteristic_eq_of_hom` consume an identification
  of coherent triples.

## Implementation notes

**Why the assembly of the reordering square is split in two.** The two routes around the square
of a coherent triple reach the modules of the punctured closed fibre by different spellings of
that scheme -- `Stacks.Algebraization.CoherentTriple.alpha` spells it as the source of
`AlgebraicGeometry.morphismRestrict`, while a statement about `(puncturedClosedFibre A f).ι`
spells it `(Stacks.Algebraization.puncturedClosedFibre A f).toScheme` -- so deciding the two
monoidal instances equal costs real heartbeats, and the pasting pays that cost once for each side
of the square. `Stacks.Algebraization.comp_eq_of_outer_squares` does the whole pasting in one
declaration and therefore in one heartbeat budget, which is not enough here; the reordering is
assembled instead from its two halves, `Stacks.Algebraization.comp_eq_of_inner_squares` and
`Stacks.Algebraization.comp_eq_of_outer_square`, in two declarations, so that each side of the
square gets a budget of its own. Everything else follows the idiom recorded in the implementation
notes of `StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleTwistSuccessor`: the
intermediate stages are stated with no ascribed type, and the generic rearrangements are stated
for an abstract category because in `X.Modules` a rewrite along
`CategoryTheory.Category.assoc` does not fire.

The route to the braiding square is the one
`Stacks.Algebraization.pullbackTensorModulesIso_associator` takes, and the
proof is the same single term: the abstract statement is
`Stacks.PullbackTensorCoherence.pullbackTensorComparison_braiding`, and the monoidal structure
it is about is `Stacks.Algebraization.strictModulesMonoidal` -- by
`Stacks.PullbackGradedAlgebra.monoidalCategory_eq`, which is `rfl` -- so the scheme statement is
the abstract one applied to the underlying morphism of ringed spaces, with nothing rewritten.
What had to be found first was the braiding instance: the statement has to be made at the
braiding *of* `strictModulesMonoidal`, and that is what `strictModulesBraided` names.

**The statement is at `β_` and not at `Stacks.Algebraization.tensorModulesBraidingIso`**, and
those are two different morphisms, not two spellings of one: `Stacks.SheafOfModules.Strict`'s
braiding is `Stacks.SheafOfModules.tensorSheafBraiding` conjugated by
`Stacks.SheafOfModules.tensorObjIso`, and the identification
`Stacks.SheafOfModules.braiding_eq_tensorSheafBraiding` is a proved lemma rather than `rfl`
(unlike this file's own coherence, which is `rfl` between its two monoidal structures). Rewriting
along it does not fire in either direction here, because its implicit arguments `O` and `hO`
have to be read off a type written as `X.Modules`, i.e. the unifier is asked to solve
`Stacks.SheafOfModules.TensorSheafification.structureSheaf ?O ?hO =?= X.ringCatSheaf`; the two
sides are equal by `rfl` (`Stacks.SheafInternalHom.structureSheaf_eq_ringCatSheaf`) but the
problem is not one the unifier solves for the metavariables. A consumer that needs the
`tensorModulesBraidingIso` spelling should therefore expect to pay for that bridge, and should
first consider whether it can be written at `β_` instead -- where `⊗` *is* `tensorModules` on
the nose, so nothing is lost.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 0F27](https://stacks.math.columbia.edu/tag/0F27)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory
open Stacks.RelativeVeryAmple

universe u

namespace Stacks.Algebraization

attribute [local instance] strictModulesMonoidal

/-- The symmetry constraint of [Stacks, Tag 01CA] as a braiding on the `𝒪_X`-modules of a
scheme, in the spelling whose tensor product is `Stacks.RelativeVeryAmple.tensorModules` on the
nose. This is the braided companion of `Stacks.Algebraization.strictModulesMonoidal`, and like
it a `local instance`: a global braiding on the sheaves of modules of a scheme would be found in
every statement about them, including those meaning a different tensor product. Activate it with
`attribute [local instance] strictModulesBraided`. -/
local instance strictModulesBraided (X : Scheme.{u}) : BraidedCategory X.Modules :=
  Stacks.SheafOfModules.Strict.braidedCategory X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X)

/-- **[Stacks, Tag 01CD] is compatible with the symmetry constraint of [Stacks, Tag 01CA]**, at
the scheme spelling: the comparison of the inverse image of a tensor product with the tensor
product of the inverse images carries the braiding to the braiding. This is
`Stacks.PullbackTensorCoherence.pullbackTensorComparison_braiding`, read at
`Stacks.Algebraization.strictModulesMonoidal` exactly as
`Stacks.Algebraization.pullbackTensorModulesIso_associator` reads the associator coherence. -/
@[reassoc]
public theorem pullbackTensorModulesIso_braiding {X S : Scheme.{u}} (g : X ⟶ S)
    (A B : S.Modules) :
    (Scheme.Modules.pullback g).map (β_ A B).hom ≫ (pullbackTensorModulesIso g B A).hom =
      (pullbackTensorModulesIso g A B).hom ≫
        (β_ ((Scheme.Modules.pullback g).obj A : X.Modules)
          ((Scheme.Modules.pullback g).obj B : X.Modules)).hom :=
  Stacks.PullbackTensorCoherence.pullbackTensorComparison_braiding g.toLRSHom.toShHom A B

/-! ### Generic rearrangements -/

/-- A square for a left whiskering, followed by a square for the whiskered morphism, pastes to a
square for the composite left whiskering. Stated for an abstract monoidal category, because in
`X.Modules` a rewrite along `CategoryTheory.Category.assoc` does not fire; see the implementation
notes of `StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleTwistSuccessor`. -/
public theorem whiskerLeft_square_comp {M : Type*} [Category M] [MonoidalCategory M]
    {E₁ E₂ Xa Y₁ Y₂ Z₁ Z₂ : M} (m : E₁ ⟶ E₂) (p₁ : E₁ ⟶ Xa ⊗ Y₁) (p₂ : E₂ ⟶ Xa ⊗ Y₂)
    (v : Y₁ ⟶ Y₂) (s₁ : Y₁ ⟶ Z₁) (s₂ : Y₂ ⟶ Z₂) (t : Z₁ ⟶ Z₂)
    (hwl : m ≫ p₂ = p₁ ≫ (Xa ◁ v)) (hbr : v ≫ s₂ = s₁ ≫ t) :
    m ≫ p₂ ≫ (Xa ◁ s₂) = (p₁ ≫ (Xa ◁ s₁)) ≫ (Xa ◁ t) := by
  rw [reassoc_of% hwl, Category.assoc, ← MonoidalCategory.whiskerLeft_comp,
    ← MonoidalCategory.whiskerLeft_comp, hbr]

/-- Three squares in a row paste to a square for the three-fold composite whose last factor is
read backwards. This is the shape of the reordering of a double tensor product: an associativity
constraint, a braiding whiskered into the first factor, and an associativity constraint back. -/
public theorem comp_eq_of_assoc_braid_squares {M : Type*} [Category M]
    {E₁ E₂ E₃ E₄ V₁ U₁ V₂ U₂ V₃ U₃ V₄ U₄ : M} (m : E₁ ⟶ E₄) (a₁ : E₁ ⟶ E₂) (bb : E₂ ⟶ E₃)
    (a₂ : E₄ ≅ E₃) (P₁ : E₂ ⟶ V₁) (w₁ : V₁ ⟶ U₁) (P₂ : E₁ ⟶ V₂) (w₂ : V₂ ⟶ U₂) (p : U₂ ⟶ U₁)
    (q : U₁ ⟶ U₃) (P₃ : E₃ ⟶ V₃) (w₃ : V₃ ⟶ U₃) (P₄ : E₄ ⟶ V₄) (w₄ : V₄ ⟶ U₄) (r : U₄ ≅ U₃)
    (hm : m = a₁ ≫ bb ≫ a₂.inv)
    (h₁ : a₁ ≫ P₁ ≫ w₁ = P₂ ≫ w₂ ≫ p)
    (h₃ : bb ≫ P₃ ≫ w₃ = (P₁ ≫ w₁) ≫ q)
    (h₂ : a₂.hom ≫ P₃ ≫ w₃ = P₄ ≫ w₄ ≫ r.hom) :
    m ≫ P₄ ≫ w₄ = P₂ ≫ w₂ ≫ (p ≫ q ≫ r.inv) := by
  have hBk : a₂.inv ≫ P₄ ≫ w₄ = P₃ ≫ w₃ ≫ r.inv := by
    rw [Iso.inv_comp_eq, reassoc_of% h₂, Iso.hom_inv_id, Category.comp_id]
  subst hm
  simp only [Category.assoc]
  rw [hBk, reassoc_of% h₃, reassoc_of% h₁]

/-- A square whose last factor is an isomorphism right-whiskered is the same square with that
factor moved, inverted, to the other side. -/
public theorem comp_eq_of_whiskerRight_square {M : Type*} [Category M] [MonoidalCategory M]
    {W V U U' Xa Ya Za : M} (e : Xa ≅ Ya) (m : W ⟶ V) (p : V ⟶ Xa ⊗ Za) (n : W ⟶ U)
    (w : U ⟶ U') (t : U' ⟶ Ya ⊗ Za) (h : m ≫ p ≫ (e.hom ▷ Za) = n ≫ w ≫ t) :
    m ≫ p = n ≫ w ≫ t ≫ (e.inv ▷ Za) := by
  rw [← reassoc_of% h]
  simp

/-- `Stacks.Algebraization.whiskerRight_tensorHom_comp_whiskerRight` with both whiskered
isomorphisms inverted: the inverse of the first, right-whiskered, carries the tensor product of
the conjugated morphism to the tensor product of the morphism. -/
public theorem whiskerRight_inv_tensorHom_comp {M : Type*} [Category M] [MonoidalCategory M]
    {Z₁ Z₂ Dk Dj Pk Pj : M} (l : Z₁ ⟶ Z₂) (p1 : Dk ≅ Pk) (j1 : Dj ≅ Pj) (q : Pk ⟶ Pj)
    (d : Dk ⟶ Dj) (hd : d = p1.hom ≫ q ≫ j1.inv) :
    (p1.inv ▷ Z₁) ≫ (d ⊗ₘ l) = (q ⊗ₘ l) ≫ (j1.inv ▷ Z₂) := by
  have h := whiskerRight_tensorHom_comp_whiskerRight l p1 j1 q d hd
  rw [← cancel_mono (j1.hom ▷ Z₂), Category.assoc, ← h]
  simp

/-- Two commuting squares sharing an edge paste to one commuting rectangle, in the shape the
middle square of the reordering of a double twist needs. -/
public theorem comp_eq_of_square_pair {C : Type*} [Category C] {W Xc Yc Zc Uc Vc : C}
    (m : W ⟶ Xc) (u : Xc ⟶ Yc) (t : Yc ⟶ Zc) (s : Xc ⟶ Uc) (v : Uc ⟶ Zc) (n : W ⟶ Vc)
    (m' : Vc ⟶ Uc) (h₁ : u ≫ t = s ≫ v) (h₂ : m ≫ s = n ≫ m') :
    m ≫ u ≫ t = n ≫ m' ≫ v := by
  rw [h₁, reassoc_of% h₂]

/-- **The reordering of a double tensor product is natural in all three factors.** The
associativity constraint, the braiding whiskered into the first factor and the associativity
constraint back carry the tensor product of three morphisms, taken in one order, to their tensor
product taken in the other. -/
public theorem assoc_braid_assoc_naturality {M : Type*} [Category M] [MonoidalCategory M]
    [BraidedCategory M] {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : M} (a : X₁ ⟶ X₂) (b : Y₁ ⟶ Y₂) (c : Z₁ ⟶ Z₂) :
    ((α_ X₁ Y₁ Z₁).hom ≫ (X₁ ◁ (β_ Y₁ Z₁).hom) ≫ (α_ X₁ Z₁ Y₁).inv) ≫ ((a ⊗ₘ c) ⊗ₘ b) =
      ((a ⊗ₘ b) ⊗ₘ c) ≫
        ((α_ X₂ Y₂ Z₂).hom ≫ (X₂ ◁ (β_ Y₂ Z₂).hom) ≫ (α_ X₂ Z₂ Y₂).inv) := by
  have key : (X₁ ◁ (β_ Y₁ Z₁).hom) ≫ (a ⊗ₘ (c ⊗ₘ b)) =
      (a ⊗ₘ (b ⊗ₘ c)) ≫ (X₂ ◁ (β_ Y₂ Z₂).hom) := by
    rw [MonoidalCategory.tensorHom_def' a (c ⊗ₘ b), MonoidalCategory.tensorHom_def' a (b ⊗ₘ c),
      ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp,
      ← BraidedCategory.braiding_naturality b c, MonoidalCategory.whiskerLeft_comp,
      Category.assoc, MonoidalCategory.whisker_exchange]
    simp only [Category.assoc]
  simp only [Category.assoc]
  rw [← MonoidalCategory.associator_inv_naturality a c b, reassoc_of% key,
    ← MonoidalCategory.associator_naturality_assoc a b c]

/-! ### The inverse-image comparison and the reordering of a double tensor product -/

/-- **[Stacks, Tag 01CD] carries the reordering of a double tensor product to the reordering**:
the associativity constraint, the braiding whiskered into the first factor and the associativity
constraint back, which together identify `(A ⊗ B) ⊗ D` with `(A ⊗ D) ⊗ B`, are carried by the
comparison of the inverse image of a tensor product with the tensor product of the inverse
images to the same composite for the inverse images.

This is the square that makes the reordering of a double twist a morphism of coherent triples; it
is pasted from `Stacks.Algebraization.pullbackTensorModulesIso_associator` in the two orders and
`Stacks.Algebraization.pullbackTensorModulesIso_braiding` in the middle. -/
public theorem pullbackTensorModulesIso_braid {X S : Scheme.{u}} (g : X ⟶ S)
    (A B D : S.Modules) :
    (Scheme.Modules.pullback g).map
          ((α_ A B D).hom ≫ (A ◁ (β_ B D).hom) ≫ (α_ A D B).inv) ≫
        (pullbackTensorModulesIso g (tensorModules S A D) B).hom =
      (pullbackTensorModulesIso g (tensorModules S A B) D).hom ≫
        (@MonoidalCategoryStruct.whiskerRight X.Modules _ _ _ _
            (pullbackTensorModulesIso g A B).hom
            ((Scheme.Modules.pullback g).obj D : X.Modules)) ≫
          ((α_ ((Scheme.Modules.pullback g).obj A : X.Modules)
                ((Scheme.Modules.pullback g).obj B : X.Modules)
                ((Scheme.Modules.pullback g).obj D : X.Modules)).hom ≫
              (((Scheme.Modules.pullback g).obj A : X.Modules) ◁
                (β_ ((Scheme.Modules.pullback g).obj B : X.Modules)
                  ((Scheme.Modules.pullback g).obj D : X.Modules)).hom) ≫
              (α_ ((Scheme.Modules.pullback g).obj A : X.Modules)
                ((Scheme.Modules.pullback g).obj D : X.Modules)
                ((Scheme.Modules.pullback g).obj B : X.Modules)).inv) ≫
            (@MonoidalCategoryStruct.whiskerRight X.Modules _ _ _ _
              (pullbackTensorModulesIso g A D).inv
              ((Scheme.Modules.pullback g).obj B : X.Modules)) := by
  have h₃ := whiskerLeft_square_comp
    ((Scheme.Modules.pullback g).map (A ◁ (β_ B D).hom))
    (pullbackTensorModulesIso g A (tensorModules S B D)).hom
    (pullbackTensorModulesIso g A (tensorModules S D B)).hom
    ((Scheme.Modules.pullback g).map (β_ B D).hom)
    (pullbackTensorModulesIso g B D).hom
    (pullbackTensorModulesIso g D B).hom
    (β_ ((Scheme.Modules.pullback g).obj B : X.Modules)
      ((Scheme.Modules.pullback g).obj D : X.Modules)).hom
    (pullbackTensorModulesIso_whiskerLeft g A (β_ B D).hom)
    (pullbackTensorModulesIso_braiding g B D)
  have hsq := comp_eq_of_assoc_braid_squares _ _ _
    ((Scheme.Modules.pullback g).mapIso (α_ A D B)) _ _ _ _ _ _ _ _ _ _
    (α_ ((Scheme.Modules.pullback g).obj A : X.Modules)
      ((Scheme.Modules.pullback g).obj D : X.Modules)
      ((Scheme.Modules.pullback g).obj B : X.Modules))
    ((CategoryTheory.Functor.map_comp _ _ _).trans
      (congrArg (fun t => (Scheme.Modules.pullback g).map (α_ A B D).hom ≫ t)
        (CategoryTheory.Functor.map_comp _ _ _)))
    (pullbackTensorModulesIso_associator g A B D) h₃
    (pullbackTensorModulesIso_associator g A D B)
  exact comp_eq_of_whiskerRight_square _ _ _ _ _ _ hsq

/-! ### The reordering of a double twist as a morphism of coherent triples -/

/-- The "outer" square of the reordering of a double twist, built from
`Stacks.Algebraization.alpha_twistZ_eq_tensorHom` by
`Stacks.Algebraization.whiskerRight_tensorHom_comp_whiskerRight`. Split off into its own
declaration, in pure term mode, so that this application gets a heartbeat budget of its own;
this is the idiom recorded in the implementation notes of
`StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleTwistSuccessor`. -/
private theorem alpha_twistZ_tensorInvertible_braid_hw {A : Type u} [CommRing A]
    [IsLocalRing A] {f : A} (T : CoherentTriple A f) {L Q : CoherentTriple A f}
    (hL : IsInvertibleTriple L) (n : ℤ) :
    letI := hL.invertible_F
    letI := hL.invertible_F₀
    MonoidalCategoryStruct.whiskerRight (C := Scheme.Modules _)
        (pullbackTensorModulesIso (morphismRestrict (closedImmersion A f)
          (Stacks.Divisors.puncturedSpectrum A)) T.F
          (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n)).hom
        ((Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
          (Stacks.Divisors.puncturedSpectrum A))).obj Q.F) ≫
      ((T.alpha.hom ⊗ₘ (hL.alphaPow n).hom) ⊗ₘ Q.alpha.hom) =
    ((T.twistZ L hL n).alpha.hom ⊗ₘ Q.alpha.hom) ≫
      MonoidalCategoryStruct.whiskerRight (C := Scheme.Modules _)
        (pullbackTensorModulesIso (puncturedClosedFibre A f).ι T.F₀
          (tensorPowScheme (closedFibre A f) L.F₀ n)).hom
        ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj Q.F₀) :=
  letI := hL.invertible_F
  letI := hL.invertible_F₀
  whiskerRight_tensorHom_comp_whiskerRight Q.alpha.hom
    (pullbackTensorModulesIso (morphismRestrict (closedImmersion A f)
      (Stacks.Divisors.puncturedSpectrum A)) T.F
      (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n))
    (pullbackTensorModulesIso (puncturedClosedFibre A f).ι T.F₀
      (tensorPowScheme (closedFibre A f) L.F₀ n))
    (T.alpha.hom ⊗ₘ (hL.alphaPow n).hom) ((T.twistZ L hL n).alpha.hom)
    (alpha_twistZ_eq_tensorHom T hL n)

/-- The "middle" square of the reordering of a double twist: the naturality of the reordering,
`Stacks.Algebraization.assoc_braid_assoc_naturality`, pasted by
`Stacks.Algebraization.comp_eq_of_square_pair` against
`Stacks.Algebraization.alpha_tensorInvertible_eq_tensorHom` read through
`Stacks.Algebraization.whiskerRight_inv_tensorHom_comp`. Split off for the same reason as
`alpha_twistZ_tensorInvertible_braid_hw`. -/
private theorem alpha_twistZ_tensorInvertible_braid_hmid {A : Type u} [CommRing A]
    [IsLocalRing A] {f : A} (T : CoherentTriple A f) {L Q : CoherentTriple A f}
    (hL : IsInvertibleTriple L) (hQ : IsInvertibleTriple Q) (n : ℤ) :
    letI := hL.invertible_F
    letI := hL.invertible_F₀
    ((α_ ((Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
            (Stacks.Divisors.puncturedSpectrum A))).obj T.F)
          ((Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
            (Stacks.Divisors.puncturedSpectrum A))).obj
            (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n))
          ((Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
            (Stacks.Divisors.puncturedSpectrum A))).obj Q.F)).hom ≫
        (Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
            (Stacks.Divisors.puncturedSpectrum A))).obj T.F ◁
          (β_ ((Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
              (Stacks.Divisors.puncturedSpectrum A))).obj
              (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n))
            ((Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
              (Stacks.Divisors.puncturedSpectrum A))).obj Q.F)).hom ≫
        (α_ ((Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
            (Stacks.Divisors.puncturedSpectrum A))).obj T.F)
          ((Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
            (Stacks.Divisors.puncturedSpectrum A))).obj Q.F)
          ((Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
            (Stacks.Divisors.puncturedSpectrum A))).obj
            (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n))).inv) ≫
      MonoidalCategoryStruct.whiskerRight (C := Scheme.Modules _)
        (pullbackTensorModulesIso (morphismRestrict (closedImmersion A f)
          (Stacks.Divisors.puncturedSpectrum A)) T.F Q.F).inv
        ((Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
          (Stacks.Divisors.puncturedSpectrum A))).obj
          (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n)) ≫
      ((T.tensorInvertible Q hQ).alpha.hom ⊗ₘ (hL.alphaPow n).hom) =
    ((T.alpha.hom ⊗ₘ (hL.alphaPow n).hom) ⊗ₘ Q.alpha.hom) ≫
      ((α_ ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj T.F₀)
          ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj
            (tensorPowScheme (closedFibre A f) L.F₀ n))
          ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj Q.F₀)).hom ≫
        (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj T.F₀ ◁
          (β_ ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj
              (tensorPowScheme (closedFibre A f) L.F₀ n))
            ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj Q.F₀)).hom ≫
        (α_ ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj T.F₀)
          ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj Q.F₀)
          ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj
            (tensorPowScheme (closedFibre A f) L.F₀ n))).inv) ≫
      MonoidalCategoryStruct.whiskerRight (C := Scheme.Modules _)
        (pullbackTensorModulesIso (puncturedClosedFibre A f).ι T.F₀ Q.F₀).inv
        ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj
          (tensorPowScheme (closedFibre A f) L.F₀ n)) :=
  letI := hL.invertible_F
  letI := hL.invertible_F₀
  comp_eq_of_square_pair _ _ _ _ _ _ _
    (whiskerRight_inv_tensorHom_comp (hL.alphaPow n).hom
      (pullbackTensorModulesIso (morphismRestrict (closedImmersion A f)
        (Stacks.Divisors.puncturedSpectrum A)) T.F Q.F)
      (pullbackTensorModulesIso (puncturedClosedFibre A f).ι T.F₀ Q.F₀)
      (T.alpha.hom ⊗ₘ Q.alpha.hom) ((T.tensorInvertible Q hQ).alpha.hom)
      (alpha_tensorInvertible_eq_tensorHom T Q hQ))
    (assoc_braid_assoc_naturality T.alpha.hom (hL.alphaPow n).hom Q.alpha.hom)

/-- The inner half of the assembly of
`Stacks.Algebraization.alpha_twistZ_tensorInvertible_braid`, with the twist's identification
already unfolded to its `⊗ₘ` form. Stated through `type_of%` of its own proof term, so that its
statement is the type that term is inferred to have, and split off so that the unification of
`Stacks.Algebraization.comp_eq_of_inner_squares`'s twelve morphism metavariables gets a heartbeat
budget of its own, separate from the ones spent computing `hmid` and `hw`. -/
private theorem alpha_twistZ_tensorInvertible_braid_inner {A : Type u} [CommRing A]
    [IsLocalRing A] {f : A} (T : CoherentTriple A f) {L Q : CoherentTriple A f}
    (hL : IsInvertibleTriple L) (hQ : IsInvertibleTriple Q) (n : ℤ) :
    type_of% (letI := hL.invertible_F
      letI := hL.invertible_F₀
      comp_eq_of_inner_squares _ _ _ _ _ _ _ _ _ _ _ _
        (pullbackTensorModulesIso_braid (morphismRestrict (closedImmersion A f)
          (Stacks.Divisors.puncturedSpectrum A)) T.F
          (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n) Q.F)
        (alpha_twistZ_tensorInvertible_braid_hmid T hL hQ n)
        (alpha_twistZ_tensorInvertible_braid_hw T (Q := Q) hL n)) := by
  have h :=
    letI := hL.invertible_F
    letI := hL.invertible_F₀
    comp_eq_of_inner_squares _ _ _ _ _ _ _ _ _ _ _ _
      (pullbackTensorModulesIso_braid (morphismRestrict (closedImmersion A f)
        (Stacks.Divisors.puncturedSpectrum A)) T.F
        (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n) Q.F)
      (alpha_twistZ_tensorInvertible_braid_hmid T hL hQ n)
      (alpha_twistZ_tensorInvertible_braid_hw T (Q := Q) hL n)
  exact h

/-- `alpha_twistZ_tensorInvertible_braid_inner` restated with its fibre-side morphisms spelled
over `(Stacks.Algebraization.puncturedClosedFibre A f).toScheme`, the spelling in which
`alpha_twistZ_tensorInvertible_braid_aux` is stated. Split off so that converting between the
two spellings of the punctured closed fibre gets a heartbeat budget of its own. -/
private theorem alpha_twistZ_tensorInvertible_braid_inner' {A : Type u} [CommRing A]
    [IsLocalRing A] {f : A} (T : CoherentTriple A f) {L Q : CoherentTriple A f}
    (hL : IsInvertibleTriple L) (hQ : IsInvertibleTriple Q) (n : ℤ) :
    letI := hL.invertible_F
    letI := hL.invertible_F₀
    (Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
          (Stacks.Divisors.puncturedSpectrum A))).map
        ((α_ T.F (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n) Q.F).hom ≫
          T.F ◁ (β_ (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n)
            Q.F).hom ≫
          (α_ T.F Q.F
            (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n)).inv) ≫
      (pullbackTensorModulesIso (morphismRestrict (closedImmersion A f)
          (Stacks.Divisors.puncturedSpectrum A))
          (tensorModules (Stacks.Divisors.puncturedSpectrum A).toScheme T.F Q.F)
          (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n)).hom ≫
      ((T.tensorInvertible Q hQ).alpha.hom ⊗ₘ (hL.alphaPow n).hom) =
    (pullbackTensorModulesIso (morphismRestrict (closedImmersion A f)
          (Stacks.Divisors.puncturedSpectrum A))
          (tensorModules (Stacks.Divisors.puncturedSpectrum A).toScheme T.F
            (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n)) Q.F).hom ≫
      ((T.twistZ L hL n).alpha.hom ⊗ₘ Q.alpha.hom) ≫
      MonoidalCategoryStruct.whiskerRight (C := Scheme.Modules _)
        (pullbackTensorModulesIso (puncturedClosedFibre A f).ι T.F₀
          (tensorPowScheme (closedFibre A f) L.F₀ n)).hom
        ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj Q.F₀) ≫
      ((α_ ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj T.F₀)
          ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj
            (tensorPowScheme (closedFibre A f) L.F₀ n))
          ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj Q.F₀)).hom ≫
        (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj T.F₀ ◁
          (β_ ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj
              (tensorPowScheme (closedFibre A f) L.F₀ n))
            ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj Q.F₀)).hom ≫
        (α_ ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj T.F₀)
          ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj Q.F₀)
          ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj
            (tensorPowScheme (closedFibre A f) L.F₀ n))).inv) ≫
      MonoidalCategoryStruct.whiskerRight (C := Scheme.Modules _)
        (pullbackTensorModulesIso (puncturedClosedFibre A f).ι T.F₀ Q.F₀).inv
        ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj
          (tensorPowScheme (closedFibre A f) L.F₀ n)) :=
  alpha_twistZ_tensorInvertible_braid_inner T hL hQ n

/-- The outer assembly of `Stacks.Algebraization.alpha_twistZ_tensorInvertible_braid`: the inner
half pasted against the reordering square on the closed-fibre side by
`Stacks.Algebraization.comp_eq_of_outer_square`. Split from
`alpha_twistZ_tensorInvertible_braid_inner` so that each of the two stages gets a heartbeat budget
of its own, which is what the two spellings of the punctured closed fibre cost here; see the
implementation notes of this file. -/
private theorem alpha_twistZ_tensorInvertible_braid_aux {A : Type u} [CommRing A]
    [IsLocalRing A] {f : A} (T : CoherentTriple A f) {L Q : CoherentTriple A f}
    (hL : IsInvertibleTriple L) (hQ : IsInvertibleTriple Q) (n : ℤ) :
    letI := hL.invertible_F
    letI := hL.invertible_F₀
    (Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
          (Stacks.Divisors.puncturedSpectrum A))).map
        ((α_ T.F (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n) Q.F).hom ≫
          T.F ◁ (β_ (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n)
            Q.F).hom ≫
          (α_ T.F Q.F
            (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n)).inv) ≫
      (pullbackTensorModulesIso (morphismRestrict (closedImmersion A f)
          (Stacks.Divisors.puncturedSpectrum A))
          (tensorModules (Stacks.Divisors.puncturedSpectrum A).toScheme T.F Q.F)
          (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n)).hom ≫
      ((T.tensorInvertible Q hQ).alpha.hom ⊗ₘ (hL.alphaPow n).hom) ≫
      (pullbackTensorModulesIso (puncturedClosedFibre A f).ι
          (tensorModules (closedFibre A f) T.F₀ Q.F₀)
          (tensorPowScheme (closedFibre A f) L.F₀ n)).inv =
    ((pullbackTensorModulesIso (morphismRestrict (closedImmersion A f)
          (Stacks.Divisors.puncturedSpectrum A))
          (tensorModules (Stacks.Divisors.puncturedSpectrum A).toScheme T.F
            (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n)) Q.F).hom ≫
        ((T.twistZ L hL n).alpha.hom ⊗ₘ Q.alpha.hom) ≫
        (pullbackTensorModulesIso (puncturedClosedFibre A f).ι
          (tensorModules (closedFibre A f) T.F₀
            (tensorPowScheme (closedFibre A f) L.F₀ n)) Q.F₀).inv) ≫
      (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map
        ((α_ T.F₀ (tensorPowScheme (closedFibre A f) L.F₀ n) Q.F₀).hom ≫
          T.F₀ ◁ (β_ (tensorPowScheme (closedFibre A f) L.F₀ n) Q.F₀).hom ≫
          (α_ T.F₀ Q.F₀ (tensorPowScheme (closedFibre A f) L.F₀ n)).inv) := by
  have h :=
    letI := hL.invertible_F
    letI := hL.invertible_F₀
    comp_eq_of_outer_square _ _ _ _ _ _ _ _ _ _ _
      (alpha_twistZ_tensorInvertible_braid_inner' T hL hQ n)
      (pullbackTensorModulesIso_braid (puncturedClosedFibre A f).ι T.F₀
        (tensorPowScheme (closedFibre A f) L.F₀ n) Q.F₀)
  exact h

/-- **The reordering of a double twist carries the identification of `(T ⊗ L^{⊗ n}) ⊗ Q` to the
identification of `(T ⊗ Q) ⊗ L^{⊗ n}`.** This is the compatibility square that makes the
reordering an isomorphism of coherent triples rather than of each member separately: it is
`Stacks.Algebraization.pullbackTensorModulesIso_braid` in each of the two routes around the
square of a coherent triple, pasted by
`Stacks.Algebraization.comp_eq_of_outer_squares` around the naturality of the reordering. -/
public theorem alpha_twistZ_tensorInvertible_braid {A : Type u} [CommRing A] [IsLocalRing A]
    {f : A} (T : CoherentTriple A f) {L Q : CoherentTriple A f} (hL : IsInvertibleTriple L)
    (hQ : IsInvertibleTriple Q) (n : ℤ) :
    letI := hL.invertible_F
    letI := hL.invertible_F₀
    (Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
          (Stacks.Divisors.puncturedSpectrum A))).map
        ((α_ T.F (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n) Q.F).hom ≫
          (T.F ◁ (β_ (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n)
            Q.F).hom) ≫
          (α_ T.F Q.F
            (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n)).inv) ≫
        ((T.tensorInvertible Q hQ).twistZ L hL n).alpha.hom =
      (pullbackTensorModulesIso (morphismRestrict (closedImmersion A f)
          (Stacks.Divisors.puncturedSpectrum A))
          (tensorModules (Stacks.Divisors.puncturedSpectrum A).toScheme T.F
            (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n)) Q.F).hom ≫
        ((T.twistZ L hL n).alpha.hom ⊗ₘ Q.alpha.hom) ≫
        (pullbackTensorModulesIso (puncturedClosedFibre A f).ι
            (tensorModules (closedFibre A f) T.F₀
              (tensorPowScheme (closedFibre A f) L.F₀ n)) Q.F₀).inv ≫
        (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map
          ((α_ T.F₀ (tensorPowScheme (closedFibre A f) L.F₀ n) Q.F₀).hom ≫
            (T.F₀ ◁ (β_ (tensorPowScheme (closedFibre A f) L.F₀ n) Q.F₀).hom) ≫
            (α_ T.F₀ Q.F₀ (tensorPowScheme (closedFibre A f) L.F₀ n)).inv) := by
  let := hL.invertible_F
  let := hL.invertible_F₀
  rw [alpha_twistZ_eq_tensorHom (T.tensorInvertible Q hQ) hL n]
  exact alpha_twistZ_tensorInvertible_braid_aux T hL hQ n

/-- **The reordering of a double twist, as a morphism of coherent triples**
`(T ⊗ L^{⊗ n}) ⊗ Q ⟶ (T ⊗ Q) ⊗ L^{⊗ n}`. Its two members are the associativity constraint, the
braiding of the two outer factors whiskered into the triple, and the associativity constraint
back; its compatibility square is
`Stacks.Algebraization.alpha_twistZ_tensorInvertible_braid` read against the `alpha` field of
`Stacks.Algebraization.CoherentTriple.tensorInvertible`.

Both members are isomorphisms
(`Stacks.Algebraization.CoherentTriple.isIso_twistZTensorInvertibleBraidHom`), so this is an
isomorphism of coherent triples in the sense the consumers of such an identification use --
`Stacks.Algebraization.CoherentTriple.ShortExact.compIso` and
`Stacks.Algebraization.CoherentTriple.eulerCharacteristic_eq_of_hom`, both of which ask for a
`Hom` with `IsIso` on each member. -/
public noncomputable def CoherentTriple.twistZTensorInvertibleBraidHom {A : Type u} [CommRing A]
    [IsLocalRing A] {f : A} (T : CoherentTriple A f) {L Q : CoherentTriple A f}
    (hL : IsInvertibleTriple L) (hQ : IsInvertibleTriple Q) (n : ℤ) :
    ((T.twistZ L hL n).tensorInvertible Q hQ).Hom ((T.tensorInvertible Q hQ).twistZ L hL n) :=
  letI := hL.invertible_F
  letI := hL.invertible_F₀
  { onPunctured :=
      (α_ T.F (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n) Q.F).hom ≫
        (T.F ◁ (β_ (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n)
          Q.F).hom) ≫
        (α_ T.F Q.F (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n)).inv
    onClosedFibre :=
      (α_ T.F₀ (tensorPowScheme (closedFibre A f) L.F₀ n) Q.F₀).hom ≫
        (T.F₀ ◁ (β_ (tensorPowScheme (closedFibre A f) L.F₀ n) Q.F₀).hom) ≫
        (α_ T.F₀ Q.F₀ (tensorPowScheme (closedFibre A f) L.F₀ n)).inv
    compatible := eq_comp_of_eq_comp_four _ _ _ _ _ _
      (alpha_twistZ_tensorInvertible_braid T hL hQ n)
      (alpha_tensorInvertible_eq_tensorHom (T.twistZ L hL n) Q hQ) }

/-- The reordering of a double tensor product is an isomorphism. -/
private theorem isIso_assoc_braid_assoc {M : Type*} [Category M] [MonoidalCategory M]
    [BraidedCategory M] (X Y Z : M) :
    IsIso ((α_ X Y Z).hom ≫ (X ◁ (β_ Y Z).hom) ≫ (α_ X Z Y).inv) :=
  Iso.isIso_hom (α_ X Y Z ≪≫ whiskerLeftIso X (β_ Y Z) ≪≫ (α_ X Z Y).symm)

/-- **Both members of the reordering of a double twist are isomorphisms**, so
`Stacks.Algebraization.CoherentTriple.twistZTensorInvertibleBraidHom` is an isomorphism of
coherent triples. -/
public theorem CoherentTriple.isIso_twistZTensorInvertibleBraidHom {A : Type u} [CommRing A]
    [IsLocalRing A] {f : A} (T : CoherentTriple A f) {L Q : CoherentTriple A f}
    (hL : IsInvertibleTriple L) (hQ : IsInvertibleTriple Q) (n : ℤ) :
    IsIso (T.twistZTensorInvertibleBraidHom hL hQ n).onPunctured ∧
      IsIso (T.twistZTensorInvertibleBraidHom hL hQ n).onClosedFibre := by
  let := hL.invertible_F
  let := hL.invertible_F₀
  exact ⟨isIso_assoc_braid_assoc _ _ _, isIso_assoc_braid_assoc _ _ _⟩

/-! ### The degree-one twist of a twist -/

/-- **The twist by `L^{⊗ n}` of a tensor product with `L` is the `(n + 1)`-st twist**, as a
morphism of coherent triples `(T ⊗ L) ⊗ L^{⊗ n} ⟶ T ⊗ L^{⊗ (n + 1)}`: the reordering of the
double twist followed by the successor identification.

This is the identification the induction step of [Stacks, Tag 0F27] needs for the *middle* term
of its short exact sequence. Twisting the degree-one sequence
`0 → T ⟶ T ⊗ L ⟶ G → 0` by `L^{⊗ n}` — which
`Stacks.Algebraization.CoherentTriple.ShortExact.twistZ` does — produces a sequence whose middle
term is `(T ⊗ L) ⊗ L^{⊗ n}`, while the clause asks for `T ⊗ L^{⊗ (n + 1)}`; this is the morphism
between them, and both of its members are isomorphisms
(`Stacks.Algebraization.CoherentTriple.isIso_tensorInvertibleTwistZSuccDegreeOneHom`). -/
public noncomputable def CoherentTriple.tensorInvertibleTwistZSuccDegreeOneHom {A : Type u}
    [CommRing A] [IsLocalRing A] {f : A} (T : CoherentTriple A f) {L : CoherentTriple A f}
    (hL : IsInvertibleTriple L) (n : ℤ) :
    ((T.tensorInvertible L hL).twistZ L hL n).Hom (T.twistZ L hL (n + 1)) :=
  letI := (T.isIso_twistZTensorInvertibleBraidHom hL hL n).1
  letI := (T.isIso_twistZTensorInvertibleBraidHom hL hL n).2
  ((T.twistZTensorInvertibleBraidHom hL hL n).inverse).comp
    (T.tensorInvertibleTwistZSuccHom hL n)

/-- **Both members of
`Stacks.Algebraization.CoherentTriple.tensorInvertibleTwistZSuccDegreeOneHom` are
isomorphisms**, so it is an isomorphism of coherent triples. -/
public theorem CoherentTriple.isIso_tensorInvertibleTwistZSuccDegreeOneHom {A : Type u}
    [CommRing A] [IsLocalRing A] {f : A} (T : CoherentTriple A f) {L : CoherentTriple A f}
    (hL : IsInvertibleTriple L) (n : ℤ) :
    IsIso (T.tensorInvertibleTwistZSuccDegreeOneHom hL n).onPunctured ∧
      IsIso (T.tensorInvertibleTwistZSuccDegreeOneHom hL n).onClosedFibre := by
  let := (T.isIso_twistZTensorInvertibleBraidHom hL hL n).1
  let := (T.isIso_twistZTensorInvertibleBraidHom hL hL n).2
  let := (T.isIso_tensorInvertibleTwistZSuccHom hL n).1
  let := (T.isIso_tensorInvertibleTwistZSuccHom hL n).2
  refine ⟨?_, ?_⟩
  · rw [show (T.tensorInvertibleTwistZSuccDegreeOneHom hL n).onPunctured =
      inv (T.twistZTensorInvertibleBraidHom hL hL n).onPunctured ≫
        (T.tensorInvertibleTwistZSuccHom hL n).onPunctured from rfl]
    infer_instance
  · rw [show (T.tensorInvertibleTwistZSuccDegreeOneHom hL n).onClosedFibre =
      inv (T.twistZTensorInvertibleBraidHom hL hL n).onClosedFibre ≫
        (T.tensorInvertibleTwistZSuccHom hL n).onClosedFibre from rfl]
    infer_instance

end Stacks.Algebraization

end
