module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatColimits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackExistence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackTensorAlongASiteMorphism
public import StacksFrontier.CategoryTheory.Sites.Modules.Gate18.FlatTensorProduct

/-! # A K-flat complex with flat terms computes the derived pullback

Let `f : (Sh(C), O) ⟶ (Sh(D), O')` be a morphism of ringed topoi. **Stacks 06YY** gives the
derived pullback `Lf^* : D(O') ⟶ D(O)` together with a canonical comparison `Lf^*K ⟶ f^*K` which
is invertible when `K` is a K-flat complex with flat terms. This file packages that
invertibility as an isomorphism

`Lf^*(QK) ≅ Q(f^*K)`

in `D(O)`, and proves it natural in `K`.

It also records the flatness of the terms of a total complex: a term of the total complex of a
bicomplex is a direct sum of its bidegrees, so it is flat as soon as every bidegree is
(**Stacks 05NG**), and for the tensor double complex of two complexes with flat terms every
bidegree is flat by **Stacks 0G6Q**. Together with **Stacks 079R** this says that the total
tensor complex of two K-flat complexes with flat terms is again K-flat with flat terms, so the
isomorphism above applies to it.

## Main results

* `Stacks.Sheaves.DerivedPullback.isFlat_total`: a term of the total complex of a bicomplex of
  flat sheaves of modules is flat.
* `Stacks.Sheaves.DerivedPullback.isFlat_tensorComplex_X`: the total tensor complex of two
  complexes with flat terms has flat terms.
* `Stacks.Sheaves.DerivedPullback.flatPullbackIso`: **a K-flat complex with flat terms computes
  the derived pullback**, `Lf^*(QK) ≅ Q(f^*K)`.
* `Stacks.Sheaves.DerivedPullback.flatPullbackIso_naturality`: that isomorphism is natural in
  the complex.

## Implementation notes

The direct sums indexing the terms of a total complex are indexed by a subtype of `ℤ × ℤ`,
which lives in `Type 0`, whereas Stacks 05NG is stated for an index type in the universe of the
sections; `isFlat_coproduct_of_smallIndex` reindexes along `Equiv.ulift`, which is the only
reason it exists.

The isomorphism `flatPullbackIso` is the comparison of Stacks 06YY with the two comparisons
`DerivedCategory.quotientCompQhIso` between `Q` and `Qh ∘ quotient` inserted at either end, so
that its source and target are written with `Q`, which is the functor the derived tensor
product of Stacks 06YU is stated against. Its naturality is accordingly the composite of three
naturality squares, one for each of the three factors.

The hypothesis that degreewise pullback followed by localization has a left derived functor is
an instance argument rather than a hypothesis of the mathematics: it is a `Prop` class, and it
is discharged for every morphism of ringed topoi whose underlying continuous functor is a
morphism of sites by
`Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy`.

## References

* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 079R](https://stacks.math.columbia.edu/tag/079R)
* [Stacks Project, Tag 0G6Q](https://stacks.math.columbia.edu/tag/0G6Q)
* [Stacks Project, Tag 05NG](https://stacks.math.columbia.edu/tag/05NG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Sheaves.DerivedPullback.KFlatPullback

namespace Stacks.Sheaves.DerivedPullback

universe u

/-! ## Flatness of the terms of a total complex -/

section Flat

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (O : Sheaf J CommRingCat.{u})

/-- **A direct sum of flat sheaves of modules indexed by a type in the lowest universe is
flat.** This is Stacks 05NG after reindexing along `Equiv.ulift`: the statement there has the
index type in the universe of the sections, and the direct sums appearing in a total complex
are indexed by a subtype of `ℤ × ℤ`. -/
theorem isFlat_coproduct_of_smallIndex {ι : Type}
    (F : ι → SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O))
    [HasCoproduct F]
    (hF : ∀ i, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := O) (F i)) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := O) (∐ F) := by
  let G : ULift.{u} ι → SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O) :=
    fun i => F i.down
  let _ : HasCoproduct G :=
    hasCoproduct_of_equiv_of_iso F G Equiv.ulift (fun _ => Iso.refl _)
  refine AlgebraicGeometry.SheafOfModules.IsFlat.of_iso O ?_
    (Stacks.SheafOfModules.FlatColimits.isFlat_coproduct (O := O) G (fun i => hF i.down))
  exact
    { hom := Sigma.desc fun i => Sigma.ι F i.down
      inv := Sigma.desc fun i => Sigma.ι G (ULift.up i)
      hom_inv_id := by apply colimit.hom_ext; rintro ⟨i⟩; simp [G]
      inv_hom_id := by apply colimit.hom_ext; rintro ⟨i⟩; simp [G] }

/-- **Every term of the total complex of a bicomplex of flat sheaves of modules is flat.** The
term in total degree `n` is the direct sum of the bidegrees `(p, q)` with `p + q = n`. -/
theorem isFlat_total
    (Z : HomologicalComplex₂ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
      (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [Z.HasTotal (ComplexShape.up ℤ)]
    (hflat : ∀ p q, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := O) ((Z.X p).X q))
    (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := O)
      ((Z.total (ComplexShape.up ℤ)).X n) :=
  isFlat_coproduct_of_smallIndex O _ (fun j => hflat j.val.1 j.val.2)

variable [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor O)
      (ComplexShape.up ℤ)]

/-- **The total tensor complex of two complexes with flat terms has flat terms.** Each bidegree
`K^p ⊗_O L^q` is flat by Stacks 0G6Q and the term in total degree `n` is their direct sum. -/
theorem isFlat_tensorComplex_X
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ)
    (hK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := O) (K.X i))
    (hL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := O) (L.X i))
    (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := O)
      ((((Stacks.SheafOfModules.Tensor.tensorComplex O).obj K).obj L).X n) :=
  isFlat_total O ((((Stacks.SheafOfModules.Tensor.sheafTensor O).mapBifunctorHomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).obj L)
    (fun p q => Stacks.SheafOfModules.FlatTensor.isFlat_tensor (K.X p) (L.X q) (hK p) (hL q)) n

end Flat

/-! ## A K-flat complex with flat terms computes the derived pullback -/

section Derived

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposSiteHom X Y)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]

/-- **A K-flat complex with flat terms computes the derived pullback.** For such a complex `K`
of `O'`-modules the derived pullback `Lf^*(QK)` is the image in `D(O)` of the degreewise
pullback `f^*K`.

This is the computation assertion of Stacks 06YY, packaged as an isomorphism with the two
comparisons between `Q` and `Qh ∘ quotient` inserted at either end. -/
def flatPullbackIso (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) K)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i)) :
    (derivedPullback f).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj ((pullbackComplex f).obj K) :=
  (derivedPullback f).mapIso ((DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).app K).symm ≪≫
    (@asIso _ _ _ _ ((derivedPullbackComparison f).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
      (Stacks.Cohomology.DerivedPullbackOnRingedTopoi.isIso_derivedPullbackComparison_app_kFlat
        f hmos K hK hflat) ≪≫
      (DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).app
          ((pullbackComplex f).obj K))

/-- **The identification of the derived pullback of a K-flat complex with flat terms with its
degreewise pullback is natural in the complex.** -/
lemma flatPullbackIso_naturality (hmos : f.u.IsMorphismOfSites Y.J X.J)
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
    (a : K ⟶ L)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) L)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hflatL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i)) :
    (derivedPullback f).map (DerivedCategory.Q.map a) ≫
        (flatPullbackIso f hmos L hL hflatL).hom =
      (flatPullbackIso f hmos K hK hflatK).hom ≫
        DerivedCategory.Q.map ((pullbackComplex f).map a) := by
  have hY := DerivedCategory.quotientCompQhIso_inv_naturality
    (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) a
  have hX := DerivedCategory.quotientCompQhIso_hom_naturality
    (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    ((pullbackComplex f).map a)
  have hC : (derivedPullback f).map (DerivedCategory.Qh.map
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map a)) ≫
        (derivedPullbackComparison f).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L) =
      (derivedPullbackComparison f).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          ((pullbackComplex f).map a)) :=
    (derivedPullbackComparison f).naturality
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map a)
  have hD : (derivedPullback f).map (DerivedCategory.Q.map a) ≫
        (derivedPullback f).map ((DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).inv.app L) =
      (derivedPullback f).map ((DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).inv.app K) ≫
        (derivedPullback f).map (DerivedCategory.Qh.map
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map a)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, hY]
  exact trans_naturality hD (trans_naturality hC hX)

end Derived

end Stacks.Sheaves.DerivedPullback

end
