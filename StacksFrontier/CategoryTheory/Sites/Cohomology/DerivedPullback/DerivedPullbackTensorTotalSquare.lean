module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorComparison

/-! # Derived pullback against the comparison with the ordinary total tensor complex

Let `f : (Sh(C), O) ⟶ (Sh(D), O')` be a morphism of ringed topoi and let `K` and `M` be cochain
complexes of `O'`-modules. **Stacks 0FPH** asserts that the square whose two paths from
`Lf^*(K ⊗^L_{O'} M)` to `Tot(f^*K ⊗_O f^*M)` are

* `Lf^*(K ⊗^L_{O'} M) ⟶ Lf^*Tot(K ⊗_{O'} M) ⟶ f^*Tot(K ⊗_{O'} M) ⟶ Tot(f^*K ⊗_O f^*M)` and
* `Lf^*(K ⊗^L_{O'} M) ⟶ Lf^*K ⊗^L_O Lf^*M ⟶ f^*K ⊗^L_O f^*M ⟶ Tot(f^*K ⊗_O f^*M)`

commutes. The horizontal maps are the canonical map from a derived tensor product to the
ordinary total tensor complex (**Stacks 06YU**), the left-hand vertical map is the comparison
of **Stacks 07A4** followed by the derived-to-degreewise pullback comparison of **Stacks 06YY**
in each tensor factor, and the right-hand vertical map is that same comparison followed by the
identification of total tensor complexes of **Stacks 03EL**.

## Main definitions

* `Stacks.Sheaves.DerivedPullback.pullbackComparisonQ`: the comparison `Lf^*(QK) ⟶ Q(f^*K)` of
  Stacks 06YY for an arbitrary complex, read between the images of the two localization
  functors `Q` and `Qh ∘ quotient`.
* `Stacks.Sheaves.DerivedPullback.bifunctorMap`: the value of a bifunctor on a pair of
  morphisms, which is how the derived tensor product of two maps is written here.
* `Stacks.Sheaves.DerivedPullback.derivedPullbackTensorComparison`: the comparison
  `Lf^*(E ⊗^L_{O'} F) ⟶ Lf^*E ⊗^L_O Lf^*F` of Stacks 07A4 at a pair of objects.

## Main results

* `Stacks.Sheaves.DerivedPullback.pullbackComparisonQ_naturality`: the comparison of
  Stacks 06YY is natural in the complex.
* `Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_hom_app_model`: on a pair of K-flat
  complexes with flat terms the comparison of Stacks 07A4 is the five-step composite
  `derivedPullbackTensorModelIso` out of which it was descended.
* `Stacks.Sheaves.DerivedPullback.derivedPullback_toTensor_square`: the square of **Stacks 0FPH**
  commutes, in the binder context of Stacks 07A4. The tag is registered one module on, in
  `DerivedPullbackTensorTotalSquareUnconditional.lean`, which discharges that context's seven
  instance arguments and so states the square with the source's hypotheses and no others.

## Implementation notes

The proof is the source's. Choosing K-flat resolutions with flat terms `P ⟶ K` and `N ⟶ M`
(**Stacks 06YS**), every arrow of the square is natural in the pair of complexes, and the arrow
`Lf^*(P ⊗^L_{O'} N) ⟶ Lf^*(K ⊗^L_{O'} M)` induced by the resolutions is invertible because `Q`
inverts quasi-isomorphisms; so it suffices to prove the square at `(P, N)`. There both paths
are identified with the two halves of the five-step chain of Stacks 07A4: the left path is its
first half followed by the comparison of total tensor complexes, and the right path is its
second half followed by the same comparison, the canonical map to the ordinary total tensor
complex being the two-sided K-flat comparison on both sides — on the target because `f^*P` and
`f^*N` are again K-flat by **Stacks 0G7E**. The square at `(P, N)` is therefore the statement
that the comparison of Stacks 07A4 at a pair of models is that chain, which is
`derivedPullbackTensorIso_hom_app_model`.

That lemma is where the descent of Stacks 07A4 along the localization of pairs of models is
read backwards: `Localization.liftNatTrans_app` evaluates the descended transformation on the
image of a pair of models, and naturality transports the value from there to the pair of
objects of `D(O')` the models represent.

`tensorComplexMap`, `pullbackTensorComplexIso` and `derivedPullbackTensorComparison` restate
three maps that already exist with their sources and targets written in terms of the total
tensor complex functor and of the derived tensor bifunctor applied to its arguments. This is
not decoration: the objects of the square are reached by the existing results under several
interchangeable spellings, and a composite whose two adjacent arrows use different ones, while
well typed, has no single syntactic object at the junction for a rewrite to match on.

The morphism-of-sites hypothesis `hmos`, the left-derived-functor instance and the collapsed
universes are those of Stacks 07A4 in this development. What `hmos` is — this development's
encoding of "`f` is a morphism of ringed topoi", not a hypothesis beyond the source's — is
spelled out in the docstring of `derivedPullback_toTensor_square`; for the collapsed universes
see the implementation notes of
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPullback/DerivedPullbackTensorComparison.lean`.
The left-derived-functor instance and the six tensor-side instance arguments are discharged in
`DerivedPullbackTensorTotalSquareUnconditional.lean`, which carries the tag.

## References

* [Stacks Project, Tag 0FPH](https://stacks.math.columbia.edu/tag/0FPH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Sheaves.DerivedPullback.KFlatPullback

namespace Stacks.Sheaves.DerivedPullback

universe u

/-! ## Diagram bookkeeping -/

section Bookkeeping

universe v₀ u₀ v₁ u₁

variable {Z : Type u₀} [Category.{v₀} Z]

/-- Two commuting squares sharing a middle column compose to a commuting square for the
composites of their horizontal edges. -/
lemma comp_naturality {A A' B B' D D' : Z} {u : A ⟶ A'} {v : B ⟶ B'} {w : D ⟶ D'}
    {x : A ⟶ B} {x' : A' ⟶ B'} {y : B ⟶ D} {y' : B' ⟶ D'}
    (hx : u ≫ x' = x ≫ v) (hy : v ≫ y' = y ≫ w) :
    u ≫ x' ≫ y' = (x ≫ y) ≫ w := by
  rw [← Category.assoc, hx, Category.assoc, hy, Category.assoc]

/-- An isomorphism transported along isomorphisms of its source and target is undone by the
isomorphism of the target. -/
lemma transportedIso_hom_comp {A B A' B' : Z} (eA : A ≅ A') (eB : B ≅ B') (g : A' ≅ B') :
    (eA ≪≫ g ≪≫ eB.symm).hom ≫ eB.hom = eA.hom ≫ g.hom := by
  rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Category.assoc, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- An isomorphism composed with the inverse of a second one, read back against that second
one. -/
lemma trans_symm_hom_comp {A C T W : Z} (e : A ≅ T) (i : C ≅ T) (k : T ⟶ W) :
    (e ≪≫ i.symm).hom ≫ i.hom ≫ k = e.hom ≫ k := by
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]

/-- Two paths of three arrows with a common source and a common target agree as soon as they
agree after a common epimorphism, each arrow of the one path being matched with the
corresponding arrow of the other by a commuting square. -/
lemma paths_eq_of_epi {A A' B B' C₁ C₁' D D' E E' W W' : Z}
    (s : A ⟶ A') [Epi s]
    (l₁ : A ⟶ B) (l₂ : B ⟶ C₁) (l₃ : C₁ ⟶ W)
    (r₁ : A ⟶ D) (r₂ : D ⟶ E) (r₃ : E ⟶ W)
    (l₁' : A' ⟶ B') (l₂' : B' ⟶ C₁') (l₃' : C₁' ⟶ W')
    (r₁' : A' ⟶ D') (r₂' : D' ⟶ E') (r₃' : E' ⟶ W')
    (lv₁ : B ⟶ B') (lv₂ : C₁ ⟶ C₁') (rv₁ : D ⟶ D') (rv₂ : E ⟶ E') (t : W ⟶ W')
    (hl₁ : s ≫ l₁' = l₁ ≫ lv₁) (hl₂ : lv₁ ≫ l₂' = l₂ ≫ lv₂) (hl₃ : lv₂ ≫ l₃' = l₃ ≫ t)
    (hr₁ : s ≫ r₁' = r₁ ≫ rv₁) (hr₂ : rv₁ ≫ r₂' = r₂ ≫ rv₂) (hr₃ : rv₂ ≫ r₃' = r₃ ≫ t)
    (h : l₁ ≫ l₂ ≫ l₃ = r₁ ≫ r₂ ≫ r₃) :
    l₁' ≫ l₂' ≫ l₃' = r₁' ≫ r₂' ≫ r₃' := by
  refine (cancel_epi s).1 ?_
  calc s ≫ l₁' ≫ l₂' ≫ l₃' = (l₁ ≫ l₂ ≫ l₃) ≫ t := by
        rw [← Category.assoc, hl₁, Category.assoc, comp_naturality hl₂ hl₃]
        simp only [Category.assoc]
    _ = (r₁ ≫ r₂ ≫ r₃) ≫ t := congrArg (· ≫ t) h
    _ = s ≫ r₁' ≫ r₂' ≫ r₃' := by
        conv_rhs => rw [← Category.assoc, hr₁, Category.assoc, comp_naturality hr₂ hr₃]
        simp only [Category.assoc]

variable {W : Type u₁} [Category.{v₁} W]

/-- The value of a bifunctor on a pair of morphisms. -/
def bifunctorMap (T : Z ⥤ Z ⥤ W) {A A' B B' : Z} (a : A ⟶ A') (b : B ⟶ B') :
    (T.obj A).obj B ⟶ (T.obj A').obj B' :=
  (T.map a).app B ≫ (T.obj A').map b

/-- The value of a bifunctor on a pair of composites is the composite of its values on the
two pairs. -/
lemma bifunctorMap_comp (T : Z ⥤ Z ⥤ W) {A A' A'' B B' B'' : Z}
    (a : A ⟶ A') (a' : A' ⟶ A'') (b : B ⟶ B') (b' : B' ⟶ B'') :
    bifunctorMap T a b ≫ bifunctorMap T a' b' = bifunctorMap T (a ≫ a') (b ≫ b') :=
  ((Functor.uncurry.obj T).map_comp ((a, b) : ((A, B) : _ × _) ⟶ (A', B'))
    ((a', b') : ((A', B') : _ × _) ⟶ (A'', B''))).symm

end Bookkeeping

/-! ## The total tensor complex of a pair of morphisms -/

section TensorComplexMap

variable (Z : RingedTopos.{u, u, u})
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O) (ComplexShape.up ℤ)]

/-- The total tensor complex `Tot(a ⊗_O b)` of a pair of morphisms of cochain complexes of
`O`-modules, with its source and target written as values of the total tensor complex
functor. -/
def tensorComplexMap
    {K K' L L' : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ}
    (a : K ⟶ K') (b : L ⟶ L') :
    ((Stacks.SheafOfModules.Tensor.tensorComplex Z.O).obj K).obj L ⟶
      ((Stacks.SheafOfModules.Tensor.tensorComplex Z.O).obj K').obj L' :=
  HomologicalComplex.mapBifunctorMap a b
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O) (ComplexShape.up ℤ)

end TensorComplexMap

/-! ## The derived-to-degreewise pullback comparison at an arbitrary complex -/

section Comparison

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

/-- **The comparison `Lf^*(QK) ⟶ Q(f^*K)` of Stacks 06YY**, from the derived pullback of a
complex of `O'`-modules to the image in `D(O)` of its degreewise pullback. It is the canonical
comparison of the derived functor with the two identifications between `Q` and `Qh ∘ quotient`
inserted at either end, and it is invertible exactly when the comparison of Stacks 06YY is. -/
def pullbackComparisonQ
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    (derivedPullback f).obj (DerivedCategory.Q.obj K) ⟶
      DerivedCategory.Q.obj ((pullbackComplex f).obj K) :=
  (derivedPullback f).map ((DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).inv.app K) ≫
    ((derivedPullbackComparison f).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) ≫
      (DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom.app
          ((pullbackComplex f).obj K))

/-- On a K-flat complex with flat terms the comparison is the isomorphism of Stacks 06YY. -/
lemma flatPullbackIso_hom_eq_pullbackComparisonQ (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) K)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i)) :
    (flatPullbackIso f hmos K hK hflat).hom = pullbackComparisonQ f K :=
  rfl

omit [X.J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [Y.J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The comparison of Stacks 06YY is natural in the complex.** -/
lemma pullbackComparisonQ_naturality
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
    (a : K ⟶ L) :
    (derivedPullback f).map (DerivedCategory.Q.map a) ≫ pullbackComparisonQ f L =
      pullbackComparisonQ f K ≫ DerivedCategory.Q.map ((pullbackComplex f).map a) := by
  have h₁ : (derivedPullback f).map (DerivedCategory.Q.map a) ≫
        (derivedPullback f).map ((DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).inv.app L) =
      (derivedPullback f).map ((DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).inv.app K) ≫
        (derivedPullback f).map (DerivedCategory.Qh.map
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map a)) := by
    rw [← Functor.map_comp, ← Functor.map_comp,
      DerivedCategory.quotientCompQhIso_inv_naturality]
  have h₂ : (derivedPullback f).map (DerivedCategory.Qh.map
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map a)) ≫
        (derivedPullbackComparison f).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L) =
      (derivedPullbackComparison f).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          ((pullbackComplex f).map a)) :=
    (derivedPullbackComparison f).naturality
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map a)
  have h₃ := DerivedCategory.quotientCompQhIso_hom_naturality
    (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    ((pullbackComplex f).map a)
  exact comp_naturality h₁ (comp_naturality h₂ h₃)

end Comparison

/-! ## Stacks 0FPH -/

section Square

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]
  (f : RingedToposSiteHom X Y)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]
  (hmos : f.u.IsMorphismOfSites Y.J X.J)

/-- **The comparison `f^*Tot(K ⊗_{O'} M) ≅ Tot(f^*K ⊗_O f^*M)` of Stacks 03EL**, with its
source and target written as values of the total tensor complex functor. -/
def pullbackTensorComplexIso
    (K M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    (pullbackComplex f).obj
        (((Stacks.SheafOfModules.Tensor.tensorComplex Y.O).obj K).obj M) ≅
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj ((pullbackComplex f).obj K)).obj
        ((pullbackComplex f).obj M) :=
  pullbackToposTensorTotalIso f hmos K M

/-- **The comparison `Lf^*(E ⊗^L_{O'} F) ⟶ Lf^*E ⊗^L_O Lf^*F` of Stacks 07A4** at a pair of
objects of `D(O')`, with its source and target written as values of the two derived tensor
bifunctors. -/
def derivedPullbackTensorComparison
    (E F : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    (derivedPullback f).obj
        (((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Y.O).tensor.obj E).obj
          F) ⟶
      ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).tensor.obj
          ((derivedPullback f).obj E)).obj ((derivedPullback f).obj F) :=
  (derivedPullbackTensorIso f hmos).hom.app (E, F)

/-- The comparison of Stacks 07A4 evaluated on the image of a pair of K-flat complexes with
flat terms is the transported value out of which it was descended. -/
lemma derivedPullbackTensorIso_hom_app_modelPair
    (PP : (IsKFlat (Y := Y)).FullSubcategory × (IsKFlat (Y := Y)).FullSubcategory) :
    (derivedPullbackTensorIso f hmos).hom.app ((flatKFlatModelPairsQ Y).obj PP) =
      (flatKFlatModelPairsTensorIso f hmos).hom.app PP := by
  have := flatKFlatModelPairsQ_isLocalization Y
  have hdef : derivedPullbackTensorIso f hmos =
      Localization.liftNatIso (flatKFlatModelPairsQ Y) (flatKFlatModelPairsW Y) _ _ _ _
        (h₁ := ⟨Iso.refl _⟩) (h₂ := ⟨Iso.refl _⟩) (flatKFlatModelPairsTensorIso f hmos) :=
    rfl
  rw [hdef, Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  simp

/-- **The comparison of Stacks 07A4 at a pair of K-flat complexes with flat terms is the
five-step composite of the source.** -/
lemma derivedPullbackTensorIso_hom_app_model
    (P N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) P)
    (hN : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) N)
    (hflatP : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (P.X i))
    (hflatN : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (N.X i)) :
    (derivedPullbackTensorIso f hmos).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj N) =
      (derivedPullbackTensorModelIso f hmos P N hP hN hflatP hflatN).hom := by
  let e := flatKFlatModelPairsIso Y
    ((⟨(HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P, ⟨hP, hflatP⟩⟩,
      ⟨(HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N, ⟨hN, hflatN⟩⟩) :
      (IsKFlat (Y := Y)).FullSubcategory × (IsKFlat (Y := Y)).FullSubcategory)
  have hnat := (derivedPullbackTensorIso f hmos).hom.naturality e.hom
  rw [derivedPullbackTensorIso_hom_app_modelPair f hmos] at hnat
  refine (cancel_epi ((Functor.uncurry.obj
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O) ⋙
    derivedPullback f).map e.hom)).1 (hnat.trans ?_)
  exact transportedIso_hom_comp
    ((Functor.uncurry.obj
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O) ⋙
      derivedPullback f).mapIso e)
    (((derivedPullback f).prod (derivedPullback f) ⋙
      Functor.uncurry.obj
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O)).mapIso e)
    (derivedPullbackTensorModelIso f hmos P N hP hN hflatP hflatN)

/-- **Stacks 0FPH at a pair of K-flat complexes with flat terms.** There both paths of the
square are halves of the five-step chain of Stacks 07A4: the canonical map to the ordinary
total tensor complex is the two-sided K-flat comparison on the source, and also on the target
since `f^*P` and `f^*N` are again K-flat by Stacks 0G7E. -/
lemma toTensor_square_of_kFlat
    (P N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) P)
    (hN : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) N)
    (hflatP : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (P.X i))
    (hflatN : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (N.X i)) :
    (derivedPullback f).map
          ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Y.O).toTensor P N) ≫
        pullbackComparisonQ f
            (((Stacks.SheafOfModules.Tensor.tensorComplex Y.O).obj P).obj N) ≫
        DerivedCategory.Q.map (pullbackTensorComplexIso f hmos P N).hom =
      derivedPullbackTensorComparison f hmos (DerivedCategory.Q.obj P)
            (DerivedCategory.Q.obj N) ≫
        bifunctorMap (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).tensor
            (pullbackComparisonQ f P) (pullbackComparisonQ f N) ≫
        (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).toTensor
          ((pullbackComplex f).obj P) ((pullbackComplex f).obj N) := by
  have hfP := kFlat_pullbackComplex' f hmos P hP hflatP
  have hfN := kFlat_pullbackComplex' f hmos N hN hflatN
  have hL : (derivedPullback f).map
          ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Y.O).toTensor P N) ≫
        pullbackComparisonQ f
          (((Stacks.SheafOfModules.Tensor.tensorComplex Y.O).obj P).obj N) =
      (derivedPullbackTensorModelLeft f hmos P N hP hN hflatP hflatN).hom := by
    rw [(Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
      Y.O).toTensor_eq_comparison P N hP hN]
    rfl
  have hR : (derivedPullbackTensorModelRight f hmos P N hP hN hflatP hflatN).hom ≫
        DerivedCategory.Q.map (pullbackTensorComplexIso f hmos P N).hom =
      bifunctorMap (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).tensor
          (pullbackComparisonQ f P) (pullbackComparisonQ f N) ≫
        (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).toTensor
          ((pullbackComplex f).obj P) ((pullbackComplex f).obj N) := by
    rw [(Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
      X.O).toTensor_eq_comparison _ _ hfP hfN]
    exact transportedIso_hom_comp
      ((Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).tensor).mapIso
        ((flatPullbackIso f hmos P hP hflatP).prod (flatPullbackIso f hmos N hN hflatN)))
      (DerivedCategory.Q.mapIso (pullbackToposTensorTotalIso f hmos P N))
      ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).comparison
        ((pullbackComplex f).obj P) ((pullbackComplex f).obj N) hfP hfN)
  have hΦ : derivedPullbackTensorComparison f hmos (DerivedCategory.Q.obj P)
        (DerivedCategory.Q.obj N) =
      (derivedPullbackTensorModelLeft f hmos P N hP hN hflatP hflatN ≪≫
        (derivedPullbackTensorModelRight f hmos P N hP hN hflatP hflatN).symm).hom :=
    derivedPullbackTensorIso_hom_app_model f hmos P N hP hN hflatP hflatN
  rw [← Category.assoc, hL, hΦ, ← hR, trans_symm_hom_comp]
  rfl

/-- **Stacks 0FPH.** For a morphism of ringed topoi `f : (Sh(C), O) ⟶ (Sh(D), O')` and cochain
complexes `K`, `M` of `O'`-modules, the square formed by the canonical maps from the derived
tensor product to the ordinary total tensor complex, the comparison
`Lf^*(K ⊗^L_{O'} M) ≅ Lf^*K ⊗^L_O Lf^*M` of Stacks 07A4 followed by the derived-to-degreewise
pullback comparison in each tensor factor, and that same comparison followed by the
identification `f^*Tot(K ⊗_{O'} M) ≅ Tot(f^*K ⊗_O f^*M)`, commutes.

`hmos` is not a hypothesis beyond the source's: it is this development's encoding of "`f` is a
morphism of ringed topoi". `AlgebraicGeometry.RingedToposSiteHom` presents the geometric
morphism by a functor `f.u` between the underlying sites and asks only that it be
*continuous*; exactness of `f^{-1}` is not a field of it, and along a merely continuous functor
the inverse image need not be exact, so such an `f` need not present a morphism of topoi at
all. `CategoryTheory.Functor.IsMorphismOfSites` is continuity together with that exactness —
it is Stacks 00X1 — and it is exactly what
`AlgebraicGeometry.RingedToposSiteHom.toToposHom` consumes to produce the underlying morphism
of topoi. Accordingly every input of the proof carries it for the same reason:
`derivedPullbackTensorIso` (Stacks 07A4), `flatPullbackIso` (Stacks 06YY),
`kFlat_pullbackComplex'` (Stacks 0G7E) and `pullbackToposTensorTotalIso` (Stacks 03EL).

The seven instance arguments of the variable block above *are* beyond the source's data:
`derivedPullback_toTensor_square_unconditional` is this theorem with the existence of `Lf^*` taken
from Stacks 06YY instead of assumed and the six tensor-side arguments left to instance search. -/
theorem derivedPullback_toTensor_square
    (K M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    (derivedPullback f).map
          ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Y.O).toTensor K M) ≫
        pullbackComparisonQ f
            (((Stacks.SheafOfModules.Tensor.tensorComplex Y.O).obj K).obj M) ≫
        DerivedCategory.Q.map (pullbackTensorComplexIso f hmos K M).hom =
      derivedPullbackTensorComparison f hmos (DerivedCategory.Q.obj K)
            (DerivedCategory.Q.obj M) ≫
        bifunctorMap (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).tensor
            (pullbackComparisonQ f K) (pullbackComparisonQ f M) ≫
        (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).toTensor
          ((pullbackComplex f).obj K) ((pullbackComplex f).obj M) := by
  obtain ⟨P, p, hP, hflatP, hp, -⟩ :=
    Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution Y.O K
  obtain ⟨N, q, hN, hflatN, hq, -⟩ :=
    Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution Y.O M
  have hp' : QuasiIso p := hp
  have hq' : QuasiIso q := hq
  have hiso : IsIso ((derivedPullback f).map
      (bifunctorMap (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Y.O).tensor
        (DerivedCategory.Q.map p) (DerivedCategory.Q.map q))) := by
    have hpair : bifunctorMap
          (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Y.O).tensor
          (DerivedCategory.Q.map p) (DerivedCategory.Q.map q) =
        ((Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Y.O).tensor).mapIso
          ((asIso (DerivedCategory.Q.map p)).prod
            (asIso (DerivedCategory.Q.map q)))).hom := rfl
    rw [hpair]
    infer_instance
  refine paths_eq_of_epi
    ((derivedPullback f).map
      (bifunctorMap (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Y.O).tensor
        (DerivedCategory.Q.map p) (DerivedCategory.Q.map q)))
    ((derivedPullback f).map
      ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Y.O).toTensor P N))
    (pullbackComparisonQ f (((Stacks.SheafOfModules.Tensor.tensorComplex Y.O).obj P).obj N))
    (DerivedCategory.Q.map (pullbackTensorComplexIso f hmos P N).hom)
    (derivedPullbackTensorComparison f hmos (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N))
    (bifunctorMap (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).tensor
      (pullbackComparisonQ f P) (pullbackComparisonQ f N))
    ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).toTensor
      ((pullbackComplex f).obj P) ((pullbackComplex f).obj N))
    ((derivedPullback f).map
      ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Y.O).toTensor K M))
    (pullbackComparisonQ f (((Stacks.SheafOfModules.Tensor.tensorComplex Y.O).obj K).obj M))
    (DerivedCategory.Q.map (pullbackTensorComplexIso f hmos K M).hom)
    (derivedPullbackTensorComparison f hmos (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj M))
    (bifunctorMap (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).tensor
      (pullbackComparisonQ f K) (pullbackComparisonQ f M))
    ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).toTensor
      ((pullbackComplex f).obj K) ((pullbackComplex f).obj M))
    ((derivedPullback f).map (DerivedCategory.Q.map (tensorComplexMap Y p q)))
    (DerivedCategory.Q.map ((pullbackComplex f).map (tensorComplexMap Y p q)))
    (bifunctorMap (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).tensor
      ((derivedPullback f).map (DerivedCategory.Q.map p))
      ((derivedPullback f).map (DerivedCategory.Q.map q)))
    (bifunctorMap (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).tensor
      (DerivedCategory.Q.map ((pullbackComplex f).map p))
      (DerivedCategory.Q.map ((pullbackComplex f).map q)))
    (DerivedCategory.Q.map
      (tensorComplexMap X ((pullbackComplex f).map p) ((pullbackComplex f).map q)))
    ?_ ?_ ?_ ?_ ?_ ?_
    (toTensor_square_of_kFlat f hmos P N hP hN hflatP hflatN)
  · rw [← Functor.map_comp, ← Functor.map_comp]
    refine congrArg (derivedPullback f).map ?_
    dsimp only [bifunctorMap]
    rw [Category.assoc]
    exact (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Y.O).toTensor_naturality
      p q
  · exact pullbackComparisonQ_naturality f (tensorComplexMap Y p q)
  · rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg DerivedCategory.Q.map
      (pullbackToposTensorTotalIso_hom_naturality f hmos p q)
  · exact (derivedPullbackTensorIso f hmos).hom.naturality
      ((DerivedCategory.Q.map p, DerivedCategory.Q.map q) :
        ((DerivedCategory.Q.obj P, DerivedCategory.Q.obj N) : _ × _) ⟶
          (DerivedCategory.Q.obj K, DerivedCategory.Q.obj M))
  · rw [bifunctorMap_comp, bifunctorMap_comp, pullbackComparisonQ_naturality f p,
      pullbackComparisonQ_naturality f q]
  · dsimp only [bifunctorMap]
    rw [Category.assoc]
    exact (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).toTensor_naturality
      ((pullbackComplex f).map p) ((pullbackComplex f).map q)

end Square

end Stacks.Sheaves.DerivedPullback

end
