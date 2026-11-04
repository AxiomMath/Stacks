module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackRelationSheaf

/-! # The sheaf of rank-`l` factorizations of `n` sections, and its inverse image

Let `(C, J)` be a site, `R` a sheaf of rings on it and `M` a sheaf of `R`-modules.  Fix `n` and
`l`.  A *rank-`l` factorization* over an object `U` consists of `n` coefficients
`a : Fin n → R(U)`, `l` generators `t : Fin l → M(U)` and an `l × n` matrix
`B : Fin l → Fin n → R(U)` such that `∑ᵢ Bₖᵢ aᵢ = 0` for every `k`.  Such a datum exhibits the
family `sᵢ = ∑ₖ Bₖᵢ tₖ` as a family of sections annihilated by the coefficients `a`, factored
through the finite free module on the `l` generators `t`; this is the shape of datum used in the
proof of Stacks 05VD, where a relation among sections of a finitely generated module has to be
pushed through a morphism of topoi.

These data are the sections of a sheaf of sets `factorizationSheaf R M n l`, cut out of the
finite product `Rⁿ ⨯ (Mˡ ⨯ (Rⁿ)ˡ)` by the vanishing of the `l` row morphisms `∑ᵢ Bₖᵢ aᵢ`.  The
file mirrors `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackRelationSheaf` exactly:
the row morphisms are built as sums of products of generalized elements, the transport statements
of `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackHomAlgebra` therefore apply to them
term by term, and the inverse image along a finite-product-preserving functor `Φ` between
categories of sheaves of sets carries the whole configuration to the corresponding configuration
for the inverse-image sheaf of rings and module of Stacks 03D2, conjugated by the canonical
comparison isomorphism.

Only the *easy* direction of the equalizer transfer is proved here: the inverse image of a
factorization is a factorization.  That direction needs no left exactness, and it is what the
application wants, since the factorization is produced downstairs and transported up.

## Main definitions

* `Stacks.Sheaves.RelationSheaf.factorizationAmbient`, `factorizationCoeff`,
  `factorizationGen`, `factorizationMatrix`: the product `Rⁿ ⨯ (Mˡ ⨯ (Rⁿ)ˡ)` and its three
  families of projections.
* `Stacks.Sheaves.RelationSheaf.factorizationRow` and `factorizationContract`: the `l` row
  morphisms `∑ᵢ Bₖᵢ aᵢ` and their joint lift into `Rˡ`.
* `Stacks.Sheaves.RelationSheaf.factorizationElt`: the `i`-th section `∑ₖ Bₖᵢ tₖ` a
  factorization exhibits.
* `Stacks.Sheaves.RelationSheaf.factorizationSheaf`: the sheaf of rank-`l` factorizations, the
  equalizer of the contraction and zero.
* `Stacks.Sheaves.ToposPullback.factorizationAmbientComparison`: the comparison isomorphism
  identifying the inverse image of `Rⁿ ⨯ (Mˡ ⨯ (Rⁿ)ˡ)` with the corresponding product for the
  inverse-image sheaf of rings and module.
* `Stacks.Sheaves.ToposPullback.factorizationSheafComparison`: **the inverse image of a
  factorization is a factorization.**

## Main results

* `Stacks.Sheaves.RelationSheaf.factorizationIota_comp_factorizationRow`: on the sheaf of
  factorizations every row vanishes.
* `Stacks.Sheaves.RelationSheaf.sections_factorizationRow` and `sections_factorizationElt`: on
  sections, the row morphisms and the exhibited sections are the expected sums.
* `Stacks.Sheaves.ToposPullback.inverseImageRingElt_factorizationRow` and
  `inverseImageModuleElt_factorizationElt`: the inverse image of a row, respectively of an
  exhibited section, is the row, respectively the exhibited section, of the inverse images.
* `Stacks.Sheaves.ToposPullback.factorizationSheafComparison_comp_factorizationIota`: the
  comparison morphism is compatible with the two inclusions into the ambient product.

## Implementation notes

**Two spellings of the inverse-image sheaf of sets.**  As in the relation-sheaf file, the
codomain of `factorizationAmbientComparison` is deliberately written with `Φ.obj (ringSheaf R)`
and `Φ.obj (moduleSheaf R M)` rather than with the underlying sheaves of
`pullbackRingSheaf J Φ R` and `pullbackModuleObj J Φ R M`.  The two spellings are equal by `rfl`
but `rw` unifies at reducible transparency and does not cross them, so every *rewrite* happens at
one fixed spelling and the crossing is performed once, in term position, by stating a
consumer-facing lemma whose proof is a bare application of the `Φ.obj`-spelled one.

**No zero morphisms.**  `Sheaf J (Type w)` has no zero morphisms, so the zero appearing in the
equalizer presentation is the zero of `CategoryTheory.Sheaf.homRing`, and
`CategoryTheory.Limits.comp_zero` does not apply to it; `CategoryTheory.Sheaf.comp_hom_ringZero`
does.  For the same reason the second morphism of the equalizer is written out as an explicit
`Limits.Pi.lift` of zeros rather than as `0`.

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
  (R : Sheaf J RingCat.{w}) (M : SheafOfModules.{w} R) (n l : ℕ)

/-- `Rⁿ ⨯ (Mˡ ⨯ (Rⁿ)ˡ)`: `n` coefficients, `l` generators, and an `l × n` matrix. -/
abbrev factorizationAmbient : Sheaf J (Type w) :=
  (∏ᶜ fun _ : Fin n => ringSheaf R) ⨯
    ((∏ᶜ fun _ : Fin l => moduleSheaf R M) ⨯
      (∏ᶜ fun _ : Fin l => ∏ᶜ fun _ : Fin n => ringSheaf R))

/-- The `i`-th coefficient of a section of `Rⁿ ⨯ (Mˡ ⨯ (Rⁿ)ˡ)`. -/
def factorizationCoeff (i : Fin n) : factorizationAmbient R M n l ⟶ ringSheaf R :=
  Limits.prod.fst ≫ Limits.Pi.π _ i

/-- The `k`-th generator of a section of `Rⁿ ⨯ (Mˡ ⨯ (Rⁿ)ˡ)`. -/
def factorizationGen (k : Fin l) : factorizationAmbient R M n l ⟶ moduleSheaf R M :=
  Limits.prod.snd ≫ Limits.prod.fst ≫ Limits.Pi.π _ k

/-- The `(k, i)`-th matrix entry of a section of `Rⁿ ⨯ (Mˡ ⨯ (Rⁿ)ˡ)`. -/
def factorizationMatrix (k : Fin l) (i : Fin n) : factorizationAmbient R M n l ⟶ ringSheaf R :=
  Limits.prod.snd ≫ Limits.prod.snd ≫ Limits.Pi.π _ k ≫ Limits.Pi.π _ i

/-- The `k`-th row of the matrix condition, `∑ᵢ Bₖᵢ aᵢ`, as a generalized element of `R`. -/
def factorizationRow (k : Fin l) : factorizationAmbient R M n l ⟶ ringSheaf R :=
  ∑ i : Fin n, factorizationMatrix R M n l k i * factorizationCoeff R M n l i

/-- The matrix condition `B ∘ a = 0`, as a morphism into `Rˡ`. -/
def factorizationContract : factorizationAmbient R M n l ⟶ ∏ᶜ fun _ : Fin l => ringSheaf R :=
  Limits.Pi.lift (factorizationRow R M n l)

/-- The constantly-zero morphism into `Rˡ`.  `Sheaf J (Type w)` has no zero morphisms, so the
target of the equalizer below is written as an explicit `Pi.lift` of zeros. -/
def factorizationZero : factorizationAmbient R M n l ⟶ ∏ᶜ fun _ : Fin l => ringSheaf R :=
  Limits.Pi.lift (fun _ : Fin l => (0 : factorizationAmbient R M n l ⟶ ringSheaf R))

/-- `∑ₖ Bₖᵢ • tₖ`: the `i`-th element of the relation a factorization factors. -/
def factorizationElt (i : Fin n) : factorizationAmbient R M n l ⟶ moduleSheaf R M :=
  ∑ k : Fin l, factorizationMatrix R M n l k i • factorizationGen R M n l k

/-- The sheaf of rank-`l` finite-free factorizations of `n` sections annihilating a coefficient
vector. -/
def factorizationSheaf : Sheaf J (Type w) :=
  Limits.equalizer (factorizationContract R M n l) (factorizationZero R M n l)

/-- The inclusion of the sheaf of rank-`l` factorizations into `Rⁿ ⨯ (Mˡ ⨯ (Rⁿ)ˡ)`. -/
def factorizationIota : factorizationSheaf R M n l ⟶ factorizationAmbient R M n l :=
  Limits.equalizer.ι _ _

/-- The defining equation of the sheaf of factorizations: the matrix condition holds on it. -/
lemma factorizationIota_comp_factorizationContract :
    factorizationIota R M n l ≫ factorizationContract R M n l =
      factorizationIota R M n l ≫ factorizationZero R M n l :=
  Limits.equalizer.condition _ _

/-- The useful form of the defining equation: on the sheaf of factorizations each of the `l`
rows `∑ᵢ Bₖᵢ aᵢ` vanishes. -/
lemma factorizationIota_comp_factorizationRow (k : Fin l) :
    factorizationIota R M n l ≫ factorizationRow R M n l k = 0 := by
  have h : (factorizationIota R M n l ≫ factorizationContract R M n l) ≫
        Limits.Pi.π (fun _ : Fin l => ringSheaf R) k =
      (factorizationIota R M n l ≫ factorizationZero R M n l) ≫
        Limits.Pi.π (fun _ : Fin l => ringSheaf R) k :=
    congrArg (fun m => m ≫ Limits.Pi.π (fun _ : Fin l => ringSheaf R) k)
      (factorizationIota_comp_factorizationContract R M n l)
  rw [Category.assoc, Category.assoc, factorizationContract, factorizationZero,
    Limits.Pi.lift_π, Limits.Pi.lift_π] at h
  rw [h, comp_hom_ringZero]

/-- On sections, the `k`-th row is the expected sum: its value at a section of
`Rⁿ ⨯ (Mˡ ⨯ (Rⁿ)ˡ)` over `X` is `∑ᵢ Bₖᵢ aᵢ`. -/
lemma sections_factorizationRow (X : Cᵒᵖ) (k : Fin l)
    (p : (sectionsFunctor J X).obj (factorizationAmbient R M n l)) :
    (sectionsFunctor J X).map (factorizationRow R M n l k) p =
      ∑ i : Fin n, (sectionsFunctor J X).map (factorizationMatrix R M n l k i) p *
        (sectionsFunctor J X).map (factorizationCoeff R M n l i) p := by
  rw [factorizationRow, sectionsFunctor_map_hom_ringSum]
  exact Finset.sum_congr rfl fun i _ => sectionsFunctor_map_hom_mul X _ _ p

/-- On sections, the `i`-th exhibited element is the expected sum: its value at a section of
`Rⁿ ⨯ (Mˡ ⨯ (Rⁿ)ˡ)` over `X` is `∑ₖ Bₖᵢ • tₖ`. -/
lemma sections_factorizationElt (X : Cᵒᵖ) (i : Fin n)
    (p : (sectionsFunctor J X).obj (factorizationAmbient R M n l)) :
    (sectionsFunctor J X).map (factorizationElt R M n l i) p =
      ∑ k : Fin l, (sectionsFunctor J X).map (factorizationMatrix R M n l k i) p •
        (sectionsFunctor J X).map (factorizationGen R M n l k) p := by
  rw [factorizationElt, sectionsFunctor_map_hom_sum]
  exact Finset.sum_congr rfl fun k _ => sectionsFunctor_map_hom_smul X _ _ p

end Stacks.Sheaves.RelationSheaf

/-! ## The inverse image of the sheaf of factorizations -/

namespace Stacks.Sheaves.ToposPullback

open Stacks.Sheaves.RelationSheaf

universe ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})]
  (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]
  (R : Sheaf K RingCat.{ww'}) (M : SheafOfModules.{ww'} R) (n l : ℕ)

omit [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})] [PreservesFiniteProducts Φ] in
/-- Precomposition distributes over a lift into a finite product.  Stated here because the
transfer of the matrix condition rewrites underneath a `Limits.Pi.lift`, and doing that with
`Limits.Pi.hom_ext` would force a projection out of one of the two spellings of the
inverse-image sheaf of rings. -/
lemma comp_piLift {X Y : Sheaf J (Type ww)} {ι : Type} [Finite ι]
    {A : ι → Sheaf J (Type ww)} (f : X ⟶ Y) (g : ∀ i, Y ⟶ A i) :
    f ≫ Limits.Pi.lift g = Limits.Pi.lift (fun i => f ≫ g i) :=
  Limits.Pi.hom_ext _ _ fun i => by
    rw [Category.assoc, Limits.Pi.lift_π, Limits.Pi.lift_π]

/-- The comparison identifying the inverse image of `Mˡ ⨯ (Rⁿ)ˡ` with the corresponding product
for the inverse-image sheaf of rings and module.  It is the inner half of
`Stacks.Sheaves.ToposPullback.factorizationAmbientComparison`, split off because the matrix
factor is a nested product and needs one extra `Limits.Pi.mapIso`. -/
def factorizationTailComparison :
    Φ.obj ((∏ᶜ fun _ : Fin l => moduleSheaf R M) ⨯
        (∏ᶜ fun _ : Fin l => ∏ᶜ fun _ : Fin n => ringSheaf R)) ≅
      (∏ᶜ fun _ : Fin l => Φ.obj (moduleSheaf R M)) ⨯
        (∏ᶜ fun _ : Fin l => ∏ᶜ fun _ : Fin n => Φ.obj (ringSheaf R)) :=
  Limits.PreservesLimitPair.iso Φ _ _ ≪≫
    Limits.prod.mapIso (Limits.PreservesProduct.iso Φ (fun _ : Fin l => moduleSheaf R M))
      (Limits.PreservesProduct.iso Φ (fun _ : Fin l => ∏ᶜ fun _ : Fin n => ringSheaf R) ≪≫
        Limits.Pi.mapIso fun _ : Fin l =>
          Limits.PreservesProduct.iso Φ (fun _ : Fin n => ringSheaf R))

/-- The comparison identifying the inverse image of the factorization ambient with the
corresponding product for the inverse-image sheaf of rings and module.

The codomain is written with `Φ.obj (ringSheaf R)` and `Φ.obj (moduleSheaf R M)` rather than with
the underlying sheaves of the inverse-image sheaf of rings and module of Stacks 03D2.  Those are
equal by `rfl`, and the consumer-facing statements below are at the second spelling; but every
*rewrite* in the proofs has to happen at one fixed spelling, since `rw` unifies at reducible
transparency and does not cross the two. -/
def factorizationAmbientComparison :
    Φ.obj (factorizationAmbient R M n l) ≅
      (∏ᶜ fun _ : Fin n => Φ.obj (ringSheaf R)) ⨯
        ((∏ᶜ fun _ : Fin l => Φ.obj (moduleSheaf R M)) ⨯
          (∏ᶜ fun _ : Fin l => ∏ᶜ fun _ : Fin n => Φ.obj (ringSheaf R))) :=
  Limits.PreservesLimitPair.iso Φ _ _ ≪≫
    Limits.prod.mapIso (Limits.PreservesProduct.iso Φ (fun _ : Fin n => ringSheaf R))
      (factorizationTailComparison J Φ R M n l)

omit [J.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})] in
/-- The tail comparison undoes the inverse image of the `k`-th generator projection. -/
lemma factorizationTailComparison_inv_comp_map_gen (k : Fin l) :
    (factorizationTailComparison J Φ R M n l).inv ≫
        Φ.map (Limits.prod.fst ≫ Limits.Pi.π (fun _ : Fin l => moduleSheaf R M) k) =
      Limits.prod.fst ≫ Limits.Pi.π (fun _ : Fin l => Φ.obj (moduleSheaf R M)) k := by
  rw [Φ.map_comp, factorizationTailComparison, Iso.trans_inv, Category.assoc,
    ← Category.assoc (Limits.PreservesLimitPair.iso Φ _ _).inv,
    Limits.PreservesLimitPair.iso_inv_fst, Limits.prod.mapIso_inv,
    ← Category.assoc (Limits.prod.map _ _), Limits.prod.map_fst, Category.assoc,
    preservesProductIso_inv_comp_map_π]

omit [J.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})] in
/-- The tail comparison undoes the inverse image of the `(k, i)`-th matrix projection. -/
lemma factorizationTailComparison_inv_comp_map_matrix (k : Fin l) (i : Fin n) :
    (factorizationTailComparison J Φ R M n l).inv ≫
        Φ.map (Limits.prod.snd ≫
          Limits.Pi.π (fun _ : Fin l => ∏ᶜ fun _ : Fin n => ringSheaf R) k ≫
            Limits.Pi.π (fun _ : Fin n => ringSheaf R) i) =
      Limits.prod.snd ≫
        Limits.Pi.π (fun _ : Fin l => ∏ᶜ fun _ : Fin n => Φ.obj (ringSheaf R)) k ≫
          Limits.Pi.π (fun _ : Fin n => Φ.obj (ringSheaf R)) i := by
  rw [Φ.map_comp, factorizationTailComparison, Iso.trans_inv, Category.assoc,
    ← Category.assoc (Limits.PreservesLimitPair.iso Φ _ _).inv,
    Limits.PreservesLimitPair.iso_inv_snd, Limits.prod.mapIso_inv,
    ← Category.assoc (Limits.prod.map _ _), Limits.prod.map_snd, Category.assoc,
    Iso.trans_inv, Φ.map_comp, Category.assoc,
    ← Category.assoc (Limits.PreservesProduct.iso Φ _).inv,
    preservesProductIso_inv_comp_map_π, ← Category.assoc (Limits.Pi.mapIso _).inv,
    Limits.Pi.mapIso_inv_π, Category.assoc, preservesProductIso_inv_comp_map_π]

omit [J.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})] in
/-- The comparison undoes the inverse image of the `i`-th coefficient projection. -/
lemma factorizationAmbientComparison_inv_comp_map_factorizationCoeff (i : Fin n) :
    (factorizationAmbientComparison J Φ R M n l).inv ≫ Φ.map (factorizationCoeff R M n l i) =
      Limits.prod.fst ≫ Limits.Pi.π (fun _ : Fin n => Φ.obj (ringSheaf R)) i := by
  rw [factorizationCoeff, Φ.map_comp, factorizationAmbientComparison, Iso.trans_inv,
    Category.assoc, ← Category.assoc (Limits.PreservesLimitPair.iso Φ _ _).inv,
    Limits.PreservesLimitPair.iso_inv_fst, Limits.prod.mapIso_inv,
    ← Category.assoc (Limits.prod.map _ _), Limits.prod.map_fst, Category.assoc,
    preservesProductIso_inv_comp_map_π]

omit [J.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})] in
/-- The comparison undoes the inverse image of the `k`-th generator projection. -/
lemma factorizationAmbientComparison_inv_comp_map_factorizationGen (k : Fin l) :
    (factorizationAmbientComparison J Φ R M n l).inv ≫ Φ.map (factorizationGen R M n l k) =
      Limits.prod.snd ≫ Limits.prod.fst ≫
        Limits.Pi.π (fun _ : Fin l => Φ.obj (moduleSheaf R M)) k := by
  rw [factorizationGen, Φ.map_comp, factorizationAmbientComparison, Iso.trans_inv,
    Category.assoc, ← Category.assoc (Limits.PreservesLimitPair.iso Φ _ _).inv,
    Limits.PreservesLimitPair.iso_inv_snd, Limits.prod.mapIso_inv,
    ← Category.assoc (Limits.prod.map _ _), Limits.prod.map_snd, Category.assoc,
    factorizationTailComparison_inv_comp_map_gen]

omit [J.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})] in
/-- The comparison undoes the inverse image of the `(k, i)`-th matrix projection. -/
lemma factorizationAmbientComparison_inv_comp_map_factorizationMatrix (k : Fin l) (i : Fin n) :
    (factorizationAmbientComparison J Φ R M n l).inv ≫
        Φ.map (factorizationMatrix R M n l k i) =
      Limits.prod.snd ≫ Limits.prod.snd ≫
        Limits.Pi.π (fun _ : Fin l => ∏ᶜ fun _ : Fin n => Φ.obj (ringSheaf R)) k ≫
          Limits.Pi.π (fun _ : Fin n => Φ.obj (ringSheaf R)) i := by
  rw [factorizationMatrix, Φ.map_comp, factorizationAmbientComparison, Iso.trans_inv,
    Category.assoc, ← Category.assoc (Limits.PreservesLimitPair.iso Φ _ _).inv,
    Limits.PreservesLimitPair.iso_inv_snd, Limits.prod.mapIso_inv,
    ← Category.assoc (Limits.prod.map _ _), Limits.prod.map_snd, Category.assoc,
    factorizationTailComparison_inv_comp_map_matrix]

/-- The inverse image of the `i`-th coefficient projection, read as a generalized element of the
inverse-image sheaf of rings, is the `i`-th coefficient projection. -/
lemma inverseImageRingElt_factorizationCoeff (i : Fin n) :
    inverseImageRingElt J Φ (factorizationAmbientComparison J Φ R M n l).inv
        (factorizationCoeff R M n l i) =
      factorizationCoeff (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n l i :=
  factorizationAmbientComparison_inv_comp_map_factorizationCoeff J Φ R M n l i

/-- The inverse image of the `k`-th generator projection, read as a generalized element of the
inverse-image module, is the `k`-th generator projection. -/
lemma inverseImageModuleElt_factorizationGen (k : Fin l) :
    inverseImageModuleElt J Φ (factorizationAmbientComparison J Φ R M n l).inv
        (factorizationGen R M n l k) =
      factorizationGen (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n l k :=
  factorizationAmbientComparison_inv_comp_map_factorizationGen J Φ R M n l k

/-- The inverse image of the `(k, i)`-th matrix projection, read as a generalized element of the
inverse-image sheaf of rings, is the `(k, i)`-th matrix projection. -/
lemma inverseImageRingElt_factorizationMatrix (k : Fin l) (i : Fin n) :
    inverseImageRingElt J Φ (factorizationAmbientComparison J Φ R M n l).inv
        (factorizationMatrix R M n l k i) =
      factorizationMatrix (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n l k i :=
  factorizationAmbientComparison_inv_comp_map_factorizationMatrix J Φ R M n l k i

/-- **The inverse image of a row is the row of the inverse images.**  This is the statement that
makes the matrix condition `B ∘ a = 0` a condition stable under inverse image. -/
theorem inverseImageRingElt_factorizationRow (k : Fin l) :
    inverseImageRingElt J Φ (factorizationAmbientComparison J Φ R M n l).inv
        (factorizationRow R M n l k) =
      factorizationRow (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n l k := by
  refine (inverseImageRingElt_sum J Φ Finset.univ
    (factorizationAmbientComparison J Φ R M n l).inv
    (fun i : Fin n =>
      factorizationMatrix R M n l k i * factorizationCoeff R M n l i)).trans ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inverseImageRingElt_mul, inverseImageRingElt_factorizationMatrix,
    inverseImageRingElt_factorizationCoeff]
  rfl

/-- **The inverse image of an exhibited element is the exhibited element of the inverse
images.**  Together with `inverseImageRingElt_factorizationRow` this says that the inverse image
of a rank-`l` factorization is a rank-`l` factorization of the inverse images. -/
theorem inverseImageModuleElt_factorizationElt (i : Fin n) :
    inverseImageModuleElt J Φ (factorizationAmbientComparison J Φ R M n l).inv
        (factorizationElt R M n l i) =
      factorizationElt (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n l i := by
  refine (inverseImageModuleElt_sum J Φ Finset.univ
    (factorizationAmbientComparison J Φ R M n l).inv
    (fun k : Fin l =>
      factorizationMatrix R M n l k i • factorizationGen R M n l k)).trans ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inverseImageModuleElt_smul, inverseImageRingElt_factorizationMatrix,
    inverseImageModuleElt_factorizationGen]
  rfl

/-- The `hom` form of `Stacks.Sheaves.ToposPullback.inverseImageRingElt_factorizationRow`: the
comparison carries the inverse image of the `k`-th row to the `k`-th row of the inverse
images. -/
lemma factorizationAmbientComparison_hom_comp_factorizationRow (k : Fin l) :
    (factorizationAmbientComparison J Φ R M n l).hom ≫
        factorizationRow (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n l k =
      Φ.map (factorizationRow R M n l k) :=
  ((Iso.inv_comp_eq _).mp (inverseImageRingElt_factorizationRow J Φ R M n l k)).symm

/-- The `hom` form of the statement that the inverse image of the zero generalized element of a
sheaf of rings is zero, at the shape the matrix condition uses. -/
lemma factorizationAmbientComparison_hom_comp_ringZero :
    (factorizationAmbientComparison J Φ R M n l).hom ≫
        (0 : factorizationAmbient (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n l ⟶
          ringSheaf (pullbackRingSheaf J Φ R)) =
      Φ.map (0 : factorizationAmbient R M n l ⟶ ringSheaf R) :=
  ((Iso.inv_comp_eq _).mp
    (inverseImageRingElt_zero J Φ (factorizationAmbientComparison J Φ R M n l).inv)).symm

omit [J.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})] in
/-- The inverse image of the matrix condition, read through the product comparison, is the lift
of the inverse images of the rows.  Stated purely at the `Φ.obj` spelling. -/
lemma map_factorizationContract_comp_piComparison :
    Φ.map (factorizationContract R M n l) ≫
        (Limits.PreservesProduct.iso Φ (fun _ : Fin l => ringSheaf R)).hom =
      Limits.Pi.lift (fun k : Fin l => Φ.map (factorizationRow R M n l k)) := by
  rw [factorizationContract, Limits.PreservesProduct.iso_hom]
  exact map_piLift_comp_piComparison J Φ _ _

omit [J.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})] in
/-- The inverse image of the zero morphism into `Rˡ`, read through the product comparison, is the
lift of the inverse images of the zeros.  Stated purely at the `Φ.obj` spelling. -/
lemma map_factorizationZero_comp_piComparison :
    Φ.map (factorizationZero R M n l) ≫
        (Limits.PreservesProduct.iso Φ (fun _ : Fin l => ringSheaf R)).hom =
      Limits.Pi.lift (fun _ : Fin l =>
        Φ.map (0 : factorizationAmbient R M n l ⟶ ringSheaf R)) := by
  rw [factorizationZero, Limits.PreservesProduct.iso_hom]
  exact map_piLift_comp_piComparison J Φ _ _

/-- A morphism that is compatible with each factor of a lift into a product carries the inverse
image of the lift to the lift, read through the product comparison. -/
private theorem comp_piLift_eq_map_piLift_comp_iso {E F : Type*} [Category E] [Category F]
    (G : E ⥤ F) {ι : Type} {A : ι → E} [HasProduct A] [HasProduct fun i => G.obj (A i)]
    [PreservesLimit (Discrete.functor A) G] {Z : E} {W : F} (e : G.obj Z ⟶ W)
    (f : ∀ i, W ⟶ G.obj (A i)) (g : ∀ i, Z ⟶ A i) (h : ∀ i, e ≫ f i = G.map (g i)) :
    e ≫ Limits.Pi.lift f = G.map (Limits.Pi.lift g) ≫ (Limits.PreservesProduct.iso G A).hom :=
  Limits.Pi.hom_ext _ _ fun i => by
    rw [Category.assoc, Limits.Pi.lift_π, h, Category.assoc, Limits.PreservesProduct.iso_hom,
      Limits.piComparison_comp_π, ← G.map_comp, Limits.Pi.lift_π]

/-- **The square for the matrix condition.**  The comparison isomorphism carries the matrix
condition of the inverse images to the inverse image of the matrix condition, read through the
product comparison.  This is the form the easy direction of the equalizer transfer needs. -/
theorem factorizationAmbientComparison_hom_comp_factorizationContract :
    (factorizationAmbientComparison J Φ R M n l).hom ≫
        factorizationContract (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n l =
      Φ.map (factorizationContract R M n l) ≫
        (Limits.PreservesProduct.iso Φ (fun _ : Fin l => ringSheaf R)).hom := by
  exact comp_piLift_eq_map_piLift_comp_iso Φ _ _ _
    (factorizationAmbientComparison_hom_comp_factorizationRow J Φ R M n l)

/-- The counterpart of
`Stacks.Sheaves.ToposPullback.factorizationAmbientComparison_hom_comp_factorizationContract` for
the zero morphism into `Rˡ`. -/
theorem factorizationAmbientComparison_hom_comp_factorizationZero :
    (factorizationAmbientComparison J Φ R M n l).hom ≫
        factorizationZero (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n l =
      Φ.map (factorizationZero R M n l) ≫
        (Limits.PreservesProduct.iso Φ (fun _ : Fin l => ringSheaf R)).hom :=
  comp_piLift_eq_map_piLift_comp_iso Φ _ _ _
    fun _ => factorizationAmbientComparison_hom_comp_ringZero J Φ R M n l

omit [J.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})] in
/-- The inverse image of the defining equation of the sheaf of factorizations, read through the
product comparison.  Stated purely at the `Φ.obj` spelling. -/
lemma map_factorizationIota_comp_map_factorizationContract_comp_piComparison :
    Φ.map (factorizationIota R M n l) ≫ Φ.map (factorizationContract R M n l) ≫
        (Limits.PreservesProduct.iso Φ (fun _ : Fin l => ringSheaf R)).hom =
      Φ.map (factorizationIota R M n l) ≫ Φ.map (factorizationZero R M n l) ≫
        (Limits.PreservesProduct.iso Φ (fun _ : Fin l => ringSheaf R)).hom := by
  rw [← Category.assoc, ← Category.assoc, ← Φ.map_comp, ← Φ.map_comp,
    factorizationIota_comp_factorizationContract]

/-- The generalized element of `Rⁿ ⨯ (Mˡ ⨯ (Rⁿ)ˡ)` underlying the inverse image of a
factorization satisfies the matrix condition of the inverse images.  This is the hypothesis the
equalizer presentation of the sheaf of factorizations needs. -/
lemma map_factorizationIota_comp_hom_comp_factorizationContract :
    (Φ.map (factorizationIota R M n l) ≫ (factorizationAmbientComparison J Φ R M n l).hom) ≫
        factorizationContract (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n l =
      (Φ.map (factorizationIota R M n l) ≫ (factorizationAmbientComparison J Φ R M n l).hom) ≫
        factorizationZero (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n l := by
  refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
  refine (congrArg (fun m => Φ.map (factorizationIota R M n l) ≫ m)
    (factorizationAmbientComparison_hom_comp_factorizationContract J Φ R M n l)).trans ?_
  refine Eq.trans ?_ (congrArg (fun m => Φ.map (factorizationIota R M n l) ≫ m)
    (factorizationAmbientComparison_hom_comp_factorizationZero J Φ R M n l).symm)
  exact map_factorizationIota_comp_map_factorizationContract_comp_piComparison J Φ R M n l

/-- **The inverse image of a factorization is a factorization.**  The morphism of sheaves of sets
from the inverse image of the sheaf of rank-`l` factorizations to the sheaf of rank-`l`
factorizations of the inverse-image sheaf of rings and module.

No left exactness is needed: the matrix condition is a polynomial identity between generalized
elements, so it survives the inverse image, and the target is an equalizer into which the
transported generalized element therefore factors. -/
def factorizationSheafComparison :
    Φ.obj (factorizationSheaf R M n l) ⟶
      factorizationSheaf (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n l :=
  Limits.equalizer.lift
    (Φ.map (factorizationIota R M n l) ≫ (factorizationAmbientComparison J Φ R M n l).hom)
    (map_factorizationIota_comp_hom_comp_factorizationContract J Φ R M n l)

/-- The comparison morphism is compatible with the two inclusions into the ambient product: the
inverse image of a factorization has the expected coefficients, generators and matrix. -/
lemma factorizationSheafComparison_comp_factorizationIota :
    factorizationSheafComparison J Φ R M n l ≫
        factorizationIota (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n l =
      Φ.map (factorizationIota R M n l) ≫ (factorizationAmbientComparison J Φ R M n l).hom :=
  Limits.equalizer.lift_ι _ _

end Stacks.Sheaves.ToposPullback

end
