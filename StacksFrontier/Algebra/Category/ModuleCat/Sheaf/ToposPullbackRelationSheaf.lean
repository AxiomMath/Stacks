module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackHomAlgebra

/-! # The sheaf of relations among `n` sections, and its inverse image

Let `(C, J)` be a site, `R` a sheaf of rings on it and `M` a sheaf of `R`-modules.  An
`n`-term *relation* among sections of `M` over an object `U` is a pair of families
`a : Fin n → R(U)`, `s : Fin n → M(U)` with `∑ᵢ aᵢ • sᵢ = 0`.  These are the sections of a
sheaf of sets `relationSheaf R M n`, cut out of the finite product `Rⁿ ⨯ Mⁿ` by the vanishing
of the contraction morphism `∑ᵢ aᵢ • sᵢ`; being a finite limit, it is carried to the
corresponding sheaf by any left exact functor.

That is what this file proves.  The contraction is built out of the scalar multiplication and
addition morphisms of `M` as a sum of generalized elements of shape `Rⁿ ⨯ Mⁿ`
(`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackHomAlgebra`), so the transport
statements of that file apply to it term by term, and the inverse image of the contraction of
`R` and `M` is the contraction of the inverse-image sheaf of rings and the inverse-image module
of Stacks 03D2 — conjugated by the canonical comparison isomorphism, which is an isomorphism
precisely because the functor preserves finite products.

## Main definitions

* `Stacks.Sheaves.RelationSheaf.relationAmbient`, `relationCoeff`, `relationElt`: the product
  `Rⁿ ⨯ Mⁿ` and its two families of projections.
* `Stacks.Sheaves.RelationSheaf.relationContract`: the contraction `∑ᵢ aᵢ • sᵢ`, as a morphism
  of sheaves of sets out of `Rⁿ ⨯ Mⁿ`.
* `Stacks.Sheaves.RelationSheaf.relationSheaf`: the sheaf of `n`-term relations, the equalizer
  of the contraction and zero.
* `Stacks.Sheaves.ToposPullback.relationAmbientComparison`: the comparison isomorphism
  identifying the inverse image of `Rⁿ ⨯ Mⁿ` with the corresponding product for the
  inverse-image sheaf of rings and module.

## Main results

* `Stacks.Sheaves.RelationSheaf.sections_relationContract`: on sections, the contraction is the
  contraction.
* `Stacks.Sheaves.ToposPullback.inv_comp_map_relationContract`: **the inverse image of the
  contraction is the contraction of the inverse images.**
* `Stacks.Sheaves.ToposPullback.relationSheafComparison` and
  `relationSheafComparison_comp_map_relationIota`: every relation among sections of the
  inverse-image module is the inverse image of a relation, as a generalized element.
* `Stacks.Sheaves.ToposPullback.relationEqualizerIso` and
  `isIso_relationSheafComparison`: that comparison is an **isomorphism** — the sheaf of
  `n`-term relations of the inverse images *is* the inverse image of the sheaf of `n`-term
  relations.  This is where left exactness of the inverse image is used, and it is the step the
  source's proof of Stacks 05VD gets from the filteredness of a comma category.

## Implementation notes

**The contraction is a sum of generalized elements, not a composite written by hand.**  Writing
`∑ᵢ aᵢ • sᵢ` as an explicit iterated composite of `moduleAddHom` and `moduleSMulHom` would need
an induction on `n` and a reindexing isomorphism `Fin (n+1) ≃ Unit ⊕ Fin n` at every step.
Instead the morphisms `Rⁿ ⨯ Mⁿ ⟶ M` are given the module structure of
`CategoryTheory.Sheaf.homModule` and the contraction is literally the sum of the products of the
projections.  Both of the statements the file exists for — the formula on sections and the
inverse-image formula — are then `Finset.sum` images of the corresponding one-term statements,
and no induction appears anywhere.

**The comparison is built as an iterated isomorphism, not as a morphism proved invertible.**
`CategoryTheory.Limits.PreservesLimitPair.iso` and `PreservesProduct.iso` are already
isomorphisms whose `hom` fields are the two comparison morphisms, so composing them gives the
comparison with its inverse in hand; asking instance search for
`IsIso (prodComparison Φ _ _ ≫ prod.map (piComparison Φ _) (piComparison Φ _))` does not
succeed, which is why it is not done that way.

**Universes.**  The two sites and the two section universes are independent throughout; no
`HasSheafify` and no smallness hypothesis is used in this file.  The equalizer exists in any
category of sheaves of types because limits of sheaves are computed objectwise.

## References

* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 08FC](https://stacks.math.columbia.edu/tag/08FC)
* [Stacks Project, Tag 05VD](https://stacks.math.columbia.edu/tag/05VD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Sheaf

universe w v u

namespace Stacks.Sheaves.RelationSheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  (R : Sheaf J RingCat.{w}) (M : SheafOfModules.{w} R) (n : ℕ)

/-- The sheaf of sets `Rⁿ ⨯ Mⁿ` whose sections over `U` are the pairs consisting of `n` sections
of the sheaf of rings and `n` sections of the sheaf of modules.  An `n`-term relation is such a
pair satisfying one equation. -/
abbrev relationAmbient : Sheaf J (Type w) :=
  (∏ᶜ fun _ : Fin n => ringSheaf R) ⨯ (∏ᶜ fun _ : Fin n => moduleSheaf R M)

/-- The `i`-th coefficient of a section of `Rⁿ ⨯ Mⁿ`. -/
def relationCoeff (i : Fin n) : relationAmbient R M n ⟶ ringSheaf R :=
  Limits.prod.fst ≫ Limits.Pi.π _ i

/-- The `i`-th element of a section of `Rⁿ ⨯ Mⁿ`. -/
def relationElt (i : Fin n) : relationAmbient R M n ⟶ moduleSheaf R M :=
  Limits.prod.snd ≫ Limits.Pi.π _ i

/-- The contraction `∑ᵢ aᵢ • sᵢ` of a section of `Rⁿ ⨯ Mⁿ`, as a morphism of sheaves of sets.
A relation is a section on which this vanishes. -/
def relationContract : relationAmbient R M n ⟶ moduleSheaf R M :=
  ∑ i : Fin n, relationCoeff R M n i • relationElt R M n i

/-- On sections, the contraction is the contraction: the value of `relationContract` at a section
of `Rⁿ ⨯ Mⁿ` over `X` is `∑ᵢ aᵢ • sᵢ` for the coefficients and elements of that section. -/
lemma sections_relationContract (X : Cᵒᵖ)
    (p : (sectionsFunctor J X).obj (relationAmbient R M n)) :
    (sectionsFunctor J X).map (relationContract R M n) p =
      ∑ i : Fin n, (sectionsFunctor J X).map (relationCoeff R M n i) p •
        (sectionsFunctor J X).map (relationElt R M n i) p := by
  rw [relationContract, sectionsFunctor_map_hom_sum]
  exact Finset.sum_congr rfl fun i _ => sectionsFunctor_map_hom_smul X _ _ p

/-- The sheaf of `n`-term relations among sections of `M`: the equalizer of the contraction and
the zero morphism out of `Rⁿ ⨯ Mⁿ`. -/
def relationSheaf : Sheaf J (Type w) :=
  Limits.equalizer (relationContract R M n) 0

/-- The inclusion of the sheaf of `n`-term relations into `Rⁿ ⨯ Mⁿ`. -/
def relationIota : relationSheaf R M n ⟶ relationAmbient R M n :=
  Limits.equalizer.ι (relationContract R M n) 0

/-- The inclusion of the sheaf of relations is a monomorphism: it is an equalizer inclusion. -/
instance mono_relationIota : Mono (relationIota R M n) :=
  inferInstanceAs (Mono (Limits.equalizer.ι (relationContract R M n) 0))

/-- A morphism into `Rⁿ ⨯ Mⁿ` whose contraction vanishes factors through the sheaf of
relations. -/
def relationLift {Z : Sheaf J (Type w)} (g : Z ⟶ relationAmbient R M n)
    (hg : g ≫ relationContract R M n = 0) : Z ⟶ relationSheaf R M n :=
  Limits.equalizer.lift g (by rw [hg, comp_hom_moduleZero])

/-- The lift of `g` through the sheaf of relations, composed with its inclusion, is `g`. -/
@[simp]
lemma relationLift_comp_relationIota {Z : Sheaf J (Type w)} (g : Z ⟶ relationAmbient R M n)
    (hg : g ≫ relationContract R M n = 0) :
    relationLift R M n g hg ≫ relationIota R M n = g :=
  Limits.equalizer.lift_ι _ _

/-- The defining equation of the sheaf of relations: the contraction vanishes on it. -/
@[simp]
lemma relationIota_comp_relationContract :
    relationIota R M n ≫ relationContract R M n = 0 :=
  (Limits.equalizer.condition (relationContract R M n) 0).trans (comp_hom_moduleZero _)

end Stacks.Sheaves.RelationSheaf

/-! ## The inverse image of the sheaf of relations -/

namespace Stacks.Sheaves.ToposPullback

open Stacks.Sheaves.RelationSheaf

universe ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})]
  (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]
  (R : Sheaf K RingCat.{ww'}) (M : SheafOfModules.{ww'} R) (n : ℕ)

/-- The canonical comparison identifying the inverse image of `Rⁿ ⨯ Mⁿ` with the product of the
inverse images.  It is an isomorphism because `Φ` preserves finite products.

The codomain is written with `Φ.obj (ringSheaf R)` and `Φ.obj (moduleSheaf R M)` rather than with
the underlying sheaves of the inverse-image sheaf of rings and module of Stacks 03D2.  Those are
equal by `rfl`, and the consumer-facing statements below are at the second spelling; but every
*rewrite* in the proofs has to happen at one fixed spelling, since `rw` unifies at reducible
transparency and does not cross the two. -/
def relationAmbientComparison :
    Φ.obj (relationAmbient R M n) ≅
      (∏ᶜ fun _ : Fin n => Φ.obj (ringSheaf R)) ⨯ (∏ᶜ fun _ : Fin n => Φ.obj (moduleSheaf R M)) :=
  Limits.PreservesLimitPair.iso Φ _ _ ≪≫
    Limits.prod.mapIso (Limits.PreservesProduct.iso Φ (fun _ : Fin n => ringSheaf R))
      (Limits.PreservesProduct.iso Φ (fun _ : Fin n => moduleSheaf R M))

omit [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})] [PreservesFiniteProducts Φ] in
/-- The inverse of a finite-product comparison undoes the inverse image of a projection. -/
lemma preservesProductIso_inv_comp_map_π {A : Fin n → Sheaf K (Type ww')}
    [Limits.PreservesLimit (Discrete.functor A) Φ] (i : Fin n) :
    (Limits.PreservesProduct.iso Φ A).inv ≫ Φ.map (Limits.Pi.π A i) =
      Limits.Pi.π (fun j => Φ.obj (A j)) i := by
  rw [Iso.inv_comp_eq, Limits.PreservesProduct.iso_hom, Limits.piComparison_comp_π]

omit [J.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})] in
/-- The comparison undoes the inverse image of the `i`-th coefficient projection. -/
lemma relationAmbientComparison_inv_comp_map_relationCoeff (i : Fin n) :
    (relationAmbientComparison J Φ R M n).inv ≫ Φ.map (relationCoeff R M n i) =
      Limits.prod.fst ≫ Limits.Pi.π (fun _ : Fin n => Φ.obj (ringSheaf R)) i := by
  rw [relationCoeff, Φ.map_comp, relationAmbientComparison, Iso.trans_inv, Category.assoc,
    ← Category.assoc (Limits.PreservesLimitPair.iso Φ _ _).inv,
    Limits.PreservesLimitPair.iso_inv_fst, Limits.prod.mapIso_inv,
    ← Category.assoc (Limits.prod.map _ _), Limits.prod.map_fst, Category.assoc,
    preservesProductIso_inv_comp_map_π]

omit [J.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})] in
/-- The comparison undoes the inverse image of the `i`-th element projection. -/
lemma relationAmbientComparison_inv_comp_map_relationElt (i : Fin n) :
    (relationAmbientComparison J Φ R M n).inv ≫ Φ.map (relationElt R M n i) =
      Limits.prod.snd ≫ Limits.Pi.π (fun _ : Fin n => Φ.obj (moduleSheaf R M)) i := by
  rw [relationElt, Φ.map_comp, relationAmbientComparison, Iso.trans_inv, Category.assoc,
    ← Category.assoc (Limits.PreservesLimitPair.iso Φ _ _).inv,
    Limits.PreservesLimitPair.iso_inv_snd, Limits.prod.mapIso_inv,
    ← Category.assoc (Limits.prod.map _ _), Limits.prod.map_snd, Category.assoc,
    preservesProductIso_inv_comp_map_π]

omit [J.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})] in
/-- The `hom` form of `relationAmbientComparison_inv_comp_map_relationCoeff`, with both sides
written at the `Φ.obj` spelling so that `rw` can use it. -/
lemma hom_comp_fstπ (i : Fin n) :
    (relationAmbientComparison J Φ R M n).hom ≫
        Limits.prod.fst ≫ Limits.Pi.π (fun _ : Fin n => Φ.obj (ringSheaf R)) i =
      Φ.map (relationCoeff R M n i) :=
  ((Iso.inv_comp_eq _).1
    (relationAmbientComparison_inv_comp_map_relationCoeff J Φ R M n i)).symm

omit [J.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})] in
/-- The `hom` form of `relationAmbientComparison_inv_comp_map_relationElt`, with both sides
written at the `Φ.obj` spelling. -/
lemma hom_comp_sndπ (i : Fin n) :
    (relationAmbientComparison J Φ R M n).hom ≫
        Limits.prod.snd ≫ Limits.Pi.π (fun _ : Fin n => Φ.obj (moduleSheaf R M)) i =
      Φ.map (relationElt R M n i) :=
  ((Iso.inv_comp_eq _).1
    (relationAmbientComparison_inv_comp_map_relationElt J Φ R M n i)).symm

omit [J.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})] in
/-- **Two generalized elements of the inverse image of `Rⁿ ⨯ Mⁿ` with the same coefficients and
the same elements agree.**  This is the joint monicity of the inverse images of the `2n`
projections, and it is how a square of morphisms into that inverse image is checked. -/
lemma hom_ext_map_relationAmbient {Z : Sheaf J (Type ww)}
    {u v : Z ⟶ Φ.obj (relationAmbient R M n)}
    (h₁ : ∀ i : Fin n, u ≫ Φ.map (relationCoeff R M n i) = v ≫ Φ.map (relationCoeff R M n i))
    (h₂ : ∀ i : Fin n, u ≫ Φ.map (relationElt R M n i) = v ≫ Φ.map (relationElt R M n i)) :
    u = v := by
  refine (Iso.cancel_iso_hom_right u v (relationAmbientComparison J Φ R M n)).1 ?_
  refine Limits.prod.hom_ext ?_ ?_ <;> refine Limits.Pi.hom_ext _ _ (fun i => ?_) <;>
    simp only [Category.assoc]
  · rw [hom_comp_fstπ]
    exact h₁ i
  · rw [hom_comp_sndπ]
    exact h₂ i

/-- The `hom` form of
`relationAmbientComparison_inv_comp_map_relationCoeff`: the comparison carries the `i`-th
coefficient projection of the inverse images to the inverse image of the `i`-th coefficient
projection. -/
lemma hom_comp_relationCoeff (i : Fin n) :
    (relationAmbientComparison J Φ R M n).hom ≫
        relationCoeff (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n i =
      Φ.map (relationCoeff R M n i) :=
  hom_comp_fstπ J Φ R M n i

/-- The `hom` form of `relationAmbientComparison_inv_comp_map_relationElt`. -/
lemma hom_comp_relationElt (i : Fin n) :
    (relationAmbientComparison J Φ R M n).hom ≫
        relationElt (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n i =
      Φ.map (relationElt R M n i) :=
  hom_comp_sndπ J Φ R M n i

/-- The inverse image of the `i`-th coefficient projection, read as a generalized element of the
inverse-image sheaf of rings, is the `i`-th coefficient projection. -/
lemma inverseImageRingElt_relationCoeff (i : Fin n) :
    inverseImageRingElt J Φ (relationAmbientComparison J Φ R M n).inv (relationCoeff R M n i) =
      relationCoeff (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n i :=
  relationAmbientComparison_inv_comp_map_relationCoeff J Φ R M n i

/-- The inverse image of the `i`-th element projection, read as a generalized element of the
inverse-image module, is the `i`-th element projection. -/
lemma inverseImageModuleElt_relationElt (i : Fin n) :
    inverseImageModuleElt J Φ (relationAmbientComparison J Φ R M n).inv (relationElt R M n i) =
      relationElt (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n i :=
  relationAmbientComparison_inv_comp_map_relationElt J Φ R M n i

/-- **The inverse image of the contraction is the contraction of the inverse images.**  This is
the statement that makes an `n`-term relation a condition stable under inverse image: the
contraction morphism of the inverse-image sheaf of rings and module is the inverse image of the
contraction morphism, conjugated by the canonical comparison isomorphism. -/
theorem inv_comp_map_relationContract :
    (relationAmbientComparison J Φ R M n).inv ≫ Φ.map (relationContract R M n) =
      relationContract (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n := by
  refine (inverseImageModuleElt_sum J Φ Finset.univ
    (relationAmbientComparison J Φ R M n).inv
    (fun i : Fin n => relationCoeff R M n i • relationElt R M n i)).trans ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inverseImageModuleElt_smul, inverseImageRingElt_relationCoeff,
    inverseImageModuleElt_relationElt]
  rfl

/-- The inverse image of the zero morphism out of `Rⁿ ⨯ Mⁿ` is the zero morphism. -/
lemma inv_comp_map_zero :
    (relationAmbientComparison J Φ R M n).inv ≫
        Φ.map (0 : relationAmbient R M n ⟶ moduleSheaf R M) =
      (0 : relationAmbient (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n ⟶
        moduleSheaf (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M)) :=
  inverseImageModuleElt_zero J Φ (relationAmbientComparison J Φ R M n).inv

/-- The generalized element of `Rⁿ ⨯ Mⁿ` underlying a relation of the inverse images equalizes
the inverse image of the contraction and the inverse image of zero.  This is the hypothesis the
equalizer presentation of the sheaf of relations needs, and it is exactly
`inv_comp_map_relationContract` together with `inv_comp_map_zero`. -/
lemma relationIota_comp_inv_comp_map_relationContract :
    (relationIota (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n ≫
        (relationAmbientComparison J Φ R M n).inv) ≫ Φ.map (relationContract R M n) =
      (relationIota (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n ≫
        (relationAmbientComparison J Φ R M n).inv) ≫
          Φ.map (0 : relationAmbient R M n ⟶ moduleSheaf R M) := by
  refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
  refine (congrArg
    (fun m => relationIota (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n ≫ m)
    (inv_comp_map_relationContract J Φ R M n)).trans ?_
  refine Eq.trans ?_ (congrArg
    (fun m => relationIota (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n ≫ m)
    (inv_comp_map_zero J Φ R M n).symm)
  exact (relationIota_comp_relationContract (pullbackRingSheaf J Φ R)
    (pullbackModuleObj J Φ R M) n).trans
      (comp_hom_moduleZero (relationIota (pullbackRingSheaf J Φ R)
        (pullbackModuleObj J Φ R M) n)).symm

/-- The morphism of sheaves of sets comparing the sheaf of `n`-term relations of the
inverse-image sheaf of rings and module with the inverse image of the sheaf of `n`-term
relations.

**This is the direction that uses left exactness**, and it is the whole point of presenting a
relation as a section of a finite limit: every relation among sections of the inverse-image
module is, as a generalized element, the inverse image of a relation downstairs.  The sheaf of
relations is an equalizer, `Φ` preserves it, and the two morphisms being equalized correspond
under the comparison isomorphism by `inv_comp_map_relationContract` and `inv_comp_map_zero`. -/
def relationSheafComparison [PreservesFiniteLimits Φ] :
    relationSheaf (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n ⟶
      Φ.obj (relationSheaf R M n) :=
  Limits.equalizer.lift
      (relationIota (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n ≫
        (relationAmbientComparison J Φ R M n).inv)
      (relationIota_comp_inv_comp_map_relationContract J Φ R M n) ≫
    (Limits.PreservesEqualizer.iso Φ (relationContract R M n) 0).inv

/-- The comparison morphism is compatible with the two inclusions into the ambient product: a
relation of the inverse images, viewed as a generalized element of the inverse image of the sheaf
of relations, has the expected coefficients and elements. -/
lemma relationSheafComparison_comp_map_relationIota [PreservesFiniteLimits Φ] :
    relationSheafComparison J Φ R M n ≫ Φ.map (relationIota R M n) =
      relationIota (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n ≫
        (relationAmbientComparison J Φ R M n).inv := by
  erw [relationSheafComparison, Category.assoc, Limits.PreservesEqualizer.iso_inv_ι,
    Limits.equalizer.lift_ι]

/-- The `hom` form of `inv_comp_map_relationContract`. -/
lemma hom_comp_relationContract :
    (relationAmbientComparison J Φ R M n).hom ≫
        relationContract (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n =
      Φ.map (relationContract R M n) :=
  ((Iso.inv_comp_eq _).1 (inv_comp_map_relationContract J Φ R M n)).symm

/-- The `hom` form of `inv_comp_map_zero`. -/
lemma hom_comp_zero :
    (relationAmbientComparison J Φ R M n).hom ≫
        (0 : relationAmbient (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n ⟶
          moduleSheaf (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M)) =
      Φ.map (0 : relationAmbient R M n ⟶ moduleSheaf R M) :=
  ((Iso.inv_comp_eq _).1 (inv_comp_map_zero J Φ R M n)).symm

/-- The generalized element of `(f⁻¹R)ⁿ ⨯ (f⁻¹M)ⁿ` underlying a point of the equalizer of the
inverse images is a relation.  This is the hypothesis needed for the morphism inverse to
`relationSheafComparison`. -/
lemma equalizerι_comp_hom_comp_relationContract :
    (Limits.equalizer.ι (Φ.map (relationContract R M n))
          (Φ.map (0 : relationAmbient R M n ⟶ moduleSheaf R M)) ≫
        (relationAmbientComparison J Φ R M n).hom) ≫
      relationContract (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n =
    (Limits.equalizer.ι (Φ.map (relationContract R M n))
          (Φ.map (0 : relationAmbient R M n ⟶ moduleSheaf R M)) ≫
        (relationAmbientComparison J Φ R M n).hom) ≫
      (0 : relationAmbient (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n ⟶
        moduleSheaf (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M)) := by
  refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
  refine (congrArg (fun m => Limits.equalizer.ι (Φ.map (relationContract R M n))
      (Φ.map (0 : relationAmbient R M n ⟶ moduleSheaf R M)) ≫ m)
    (hom_comp_relationContract J Φ R M n)).trans ?_
  refine (Limits.equalizer.condition _ _).trans ?_
  exact (congrArg (fun m => Limits.equalizer.ι (Φ.map (relationContract R M n))
      (Φ.map (0 : relationAmbient R M n ⟶ moduleSheaf R M)) ≫ m)
    (hom_comp_zero J Φ R M n)).symm

/-- The morphism of sheaves of relations inverse to the one `relationSheafComparison` is built
from. -/
def relationEqualizerInv :
    Limits.equalizer (Φ.map (relationContract R M n))
        (Φ.map (0 : relationAmbient R M n ⟶ moduleSheaf R M)) ⟶
      relationSheaf (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n :=
  Limits.equalizer.lift
    (Limits.equalizer.ι (Φ.map (relationContract R M n))
        (Φ.map (0 : relationAmbient R M n ⟶ moduleSheaf R M)) ≫
      (relationAmbientComparison J Φ R M n).hom)
    (equalizerι_comp_hom_comp_relationContract J Φ R M n)

/-- The morphism `relationSheafComparison` is built from, isolated. -/
def relationEqualizerHom :
    relationSheaf (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n ⟶
      Limits.equalizer (Φ.map (relationContract R M n))
        (Φ.map (0 : relationAmbient R M n ⟶ moduleSheaf R M)) :=
  Limits.equalizer.lift
    (relationIota (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n ≫
      (relationAmbientComparison J Φ R M n).inv)
    (relationIota_comp_inv_comp_map_relationContract J Φ R M n)

/-- `relationEqualizerHom` followed by the inclusion into the ambient product. -/
lemma relationEqualizerHom_comp_ι :
    relationEqualizerHom J Φ R M n ≫
        Limits.equalizer.ι (Φ.map (relationContract R M n))
          (Φ.map (0 : relationAmbient R M n ⟶ moduleSheaf R M)) =
      relationIota (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n ≫
        (relationAmbientComparison J Φ R M n).inv :=
  Limits.equalizer.lift_ι _ _

/-- `relationEqualizerInv` followed by the inclusion into the ambient product. -/
lemma relationEqualizerInv_comp_relationIota :
    relationEqualizerInv J Φ R M n ≫
        relationIota (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n =
      Limits.equalizer.ι (Φ.map (relationContract R M n))
          (Φ.map (0 : relationAmbient R M n ⟶ moduleSheaf R M)) ≫
        (relationAmbientComparison J Φ R M n).hom :=
  Limits.equalizer.lift_ι _ _

/-- The sheaf of relations of the inverse images is the equalizer of the inverse images of the
contraction and of zero. -/
def relationEqualizerIso :
    relationSheaf (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n ≅
      Limits.equalizer (Φ.map (relationContract R M n))
        (Φ.map (0 : relationAmbient R M n ⟶ moduleSheaf R M)) where
  hom := relationEqualizerHom J Φ R M n
  inv := relationEqualizerInv J Φ R M n
  hom_inv_id := by
    refine Limits.equalizer.hom_ext ?_
    refine (Category.assoc _ _ _).trans ?_
    refine Eq.trans (congrArg (fun m => relationEqualizerHom J Φ R M n ≫ m)
      (relationEqualizerInv_comp_relationIota J Φ R M n)) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun m => m ≫ (relationAmbientComparison J Φ R M n).hom)
      (relationEqualizerHom_comp_ι J Φ R M n)) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg
      (fun m => relationIota (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n ≫ m)
      (relationAmbientComparison J Φ R M n).inv_hom_id) ?_
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  inv_hom_id := by
    refine Limits.equalizer.hom_ext ?_
    refine (Category.assoc _ _ _).trans ?_
    refine Eq.trans (congrArg (fun m => relationEqualizerInv J Φ R M n ≫ m)
      (relationEqualizerHom_comp_ι J Φ R M n)) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun m => m ≫ (relationAmbientComparison J Φ R M n).inv)
      (relationEqualizerInv_comp_relationIota J Φ R M n)) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg
      (fun m => Limits.equalizer.ι (Φ.map (relationContract R M n))
        (Φ.map (0 : relationAmbient R M n ⟶ moduleSheaf R M)) ≫ m)
      (relationAmbientComparison J Φ R M n).hom_inv_id) ?_
    exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- **The comparison morphism is an isomorphism.**  A relation among sections of the
inverse-image module is not merely the image of a relation downstairs: the sheaf of relations of
the inverse images *is* the inverse image of the sheaf of relations. -/
instance isIso_relationSheafComparison [PreservesFiniteLimits Φ] :
    IsIso (relationSheafComparison J Φ R M n) :=
  ((relationEqualizerIso J Φ R M n).trans
    (Limits.PreservesEqualizer.iso Φ (relationContract R M n) 0).symm).isIso_hom

/-- The sheaf of `n`-term relations of the inverse images, as an isomorphism onto the inverse
image of the sheaf of `n`-term relations. -/
def relationSheafIsoPullback [PreservesFiniteLimits Φ] :
    relationSheaf (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n ≅
      Φ.obj (relationSheaf R M n) :=
  asIso (relationSheafComparison J Φ R M n)

/-- The inverse of the comparison, followed by the inclusion of the sheaf of relations of the
inverse images into its ambient product. -/
lemma relationSheafIsoPullback_inv_comp_relationIota [PreservesFiniteLimits Φ] :
    (relationSheafIsoPullback J Φ R M n).inv ≫
        relationIota (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n =
      Φ.map (relationIota R M n) ≫ (relationAmbientComparison J Φ R M n).hom := by
  erw [Iso.inv_comp_eq, ← Category.assoc, relationSheafIsoPullback, asIso_hom,
    relationSheafComparison_comp_map_relationIota, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

end Stacks.Sheaves.ToposPullback

end
