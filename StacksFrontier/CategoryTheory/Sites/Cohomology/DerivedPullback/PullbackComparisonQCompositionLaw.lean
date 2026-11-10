module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CompositionOnRingedTopoi
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorTotalSquare

/-!
# The comparison `Lf^*(QM) ⟶ Q(f^*M)` along a composite of morphisms of ringed topoi

Let `f : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` and `g : (Sh(D), 𝒪_D) ⟶ (Sh(E), 𝒪_E)` be morphisms of
ringed topoi.  `Stacks.Sheaves.DerivedPullback.pullbackComparisonQ` is the comparison

`Lf^*(QM) ⟶ Q(f^*M)`

of Stacks 06YY, from the derived pullback of a cochain complex to the image in `D(𝒪_C)` of its
degreewise pullback.  This file proves that it is compatible with composition: the comparison
for `g ∘ f`, read through the composition isomorphism `Lg^* ⋙ Lf^* ≅ L(g ∘ f)^*` of Stacks 0D6D,
is the comparison for `g` followed by the comparison for `f`, followed by the composition law
for degreewise pullback of complexes.

## Main definitions

* `Stacks.Sheaves.DerivedPullback.CompositionLaw.pullbackComplexCompIso`: the composition law
  `g^* ⋙ f^* ≅ (g ∘ f)^*` for degreewise pullback, read on cochain complexes.

## Main results

* `Stacks.Sheaves.DerivedPullback.CompositionLaw.pullbackComplexCompIso_hom_app_f`: in a single
  degree, the composition law on complexes is the underived composition law
  `AlgebraicGeometry.RingedToposSiteHom.pullbackToposCompIso` at the term of that degree.
* `CompositionLaw.pullbackOnHomotopyCompIso_hom_app_comp_quotientCompQhIso`: on the image of a
  cochain complex, the pullback-composition isomorphism of the homotopy categories agrees, across
  the `Q` versus `Qh ∘ quotient` bridge `CategoryTheory.DerivedCategory.quotientCompQhIso`, with
  the pullback-composition isomorphism of complexes.
* `CompositionLaw.derivedPullbackCompIso_hom_app_comp_pullbackComparisonQ`: **the composition
  law for the comparison of Stacks 06YY**, at the `DerivedCategory.Q` level.

## References

* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Cohomology.DerivedPullbackCompositionOnTopoi
open Stacks.Sheaves.DerivedPullback.KFlatPullback

namespace Stacks.Sheaves.DerivedPullback.CompositionLaw

universe u

/-- Let `Lf : DY ⥤ DX` be a functor, `ℓ ≫ e ≫ b` a chain of morphisms of `DY` with `b'` a
retraction of `b`, and `d, m, d', ε, εf, κ, β, βW, q` morphisms of `DX`. If
`d ≫ m = Lf.map ℓ ≫ d'`, `d' ≫ ε = Lf.map e ≫ εf ≫ κ` and `κ ≫ β = βW ≫ q`, then
`d ≫ m ≫ ε ≫ β = Lf.map (ℓ ≫ e ≫ b) ≫ (Lf.map b' ≫ εf ≫ βW) ≫ q`. -/
lemma comp_of_three_factors {DY DX : Type*} [Category DY] [Category DX] (Lf : DY ⥤ DX)
    {y₀ y₁ y₂ y₃ : DY} {ℓ : y₀ ⟶ y₁} {e : y₁ ⟶ y₂} {b : y₂ ⟶ y₃} {b' : y₃ ⟶ y₂}
    {T T' U V W V' : DX}
    {d : Lf.obj y₀ ⟶ T} {m : T ⟶ T'} {d' : Lf.obj y₁ ⟶ T'} {ε : T' ⟶ U}
    {εf : Lf.obj y₂ ⟶ W} {κ : W ⟶ U} {β : U ⟶ V} {βW : W ⟶ V'} {q : V' ⟶ V}
    (hnat : d ≫ m = Lf.map ℓ ≫ d')
    (hfac : d' ≫ ε = Lf.map e ≫ εf ≫ κ)
    (hb : κ ≫ β = βW ≫ q)
    (hcancel : b ≫ b' = 𝟙 y₂) :
    d ≫ m ≫ ε ≫ β = Lf.map (ℓ ≫ e ≫ b) ≫ (Lf.map b' ≫ εf ≫ βW) ≫ q := by
  have hcancel' : Lf.map b ≫ Lf.map b' = 𝟙 _ := by rw [← Lf.map_comp, hcancel, Lf.map_id]
  simp only [reassoc_of% hnat, reassoc_of% hfac, hb, Functor.map_comp, Category.assoc,
    reassoc_of% hcancel']

variable {X Y Z : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The composition law for degreewise pullback on cochain complexes.**  For composable
morphisms of ringed topoi `f : X ⟶ Y`, `g : Y ⟶ Z`, degreewise pullback along `g` followed by
degreewise pullback along `f` is degreewise pullback along `g ∘ f`, by the isomorphism
`CategoryTheory.Functor.mapHomologicalComplexCompIso` induced by the underived composition law
`AlgebraicGeometry.RingedToposSiteHom.pullbackToposCompIso`. -/
def pullbackComplexCompIso (f : RingedToposSiteHom X Y) (g : RingedToposSiteHom Y Z) :
    pullbackComplex g ⋙ pullbackComplex f ≅ pullbackComplex (g.comp f) :=
  Functor.mapHomologicalComplexCompIso
    (AlgebraicGeometry.RingedToposSiteHom.pullbackToposCompIso f g) (ComplexShape.up ℤ)

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The composition law for degreewise pullback on complexes, in a single degree: it is the
underived composition law at the term of that degree. -/
lemma pullbackComplexCompIso_hom_app_f (f : RingedToposSiteHom X Y)
    (g : RingedToposSiteHom Y Z)
    (M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ)
    (n : ℤ) :
    ((pullbackComplexCompIso f g).hom.app M).f n =
      (AlgebraicGeometry.RingedToposSiteHom.pullbackToposCompIso f g).hom.app (M.X n) :=
  rfl

section Main

attribute [local instance] HasDerivedCategory.standard

variable (f : RingedToposSiteHom X Y) (g : RingedToposSiteHom Y Z)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy g).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
      (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy (g.comp f)).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
      (ComplexShape.up ℤ))]

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy g).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
      (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy (g.comp f)).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
      (ComplexShape.up ℤ))] in
/-- **The two pullback-composition isomorphisms agree across the `Q` versus `Qh ∘ quotient`
bridge.**  On the homotopy categories the isomorphism is
`Stacks.Cohomology.DerivedPullbackCompositionOnTopoi.pullbackOnHomotopyCompIso`, on complexes it
is `pullbackComplexCompIso`, and
`CategoryTheory.DerivedCategory.quotientCompQhIso` identifies the two levels. -/
theorem pullbackOnHomotopyCompIso_hom_app_comp_quotientCompQhIso
    (M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ) :
    DerivedCategory.Qh.map ((pullbackOnHomotopyCompIso f g).hom.app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M)) ≫
        (DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom.app
            ((pullbackComplex (g.comp f)).obj M) =
      (DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom.app
            ((pullbackComplex f).obj ((pullbackComplex g).obj M)) ≫
        DerivedCategory.Q.map ((pullbackComplexCompIso f g).hom.app M) :=
  DerivedCategory.quotientCompQhIso_hom_naturality ((pullbackComplexCompIso f g).hom.app M)

/-- The value of `Stacks.Sheaves.DerivedPullback.pullbackComparisonQ` at a cochain complex, written
out as a composite of three maps. -/
private lemma pullbackComparisonQ_eq {X Y : RingedTopos.{u, u, u}}
    [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (f : RingedToposSiteHom X Y)
    [(pullbackOnHomotopy f).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (ComplexShape.up ℤ))]
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    pullbackComparisonQ f K =
      (derivedPullback f).map ((DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).inv.app K) ≫
        (derivedPullbackComparison f).app
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) ≫
          (DerivedCategory.quotientCompQhIso
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom.app
              ((pullbackComplex f).obj K) :=
  rfl

/-- **The composition law for the comparison `Lf^*(QM) ⟶ Q(f^*M)` of Stacks 06YY.**  For
composable morphisms of ringed topoi `f : X ⟶ Y`, `g : Y ⟶ Z` and an arbitrary cochain complex
`M` of `𝒪_Z`-modules, the composition isomorphism `Lg^* ⋙ Lf^* ≅ L(g ∘ f)^*` of Stacks 0D6D
carries the comparison for `g ∘ f` to the comparison for `g`, then the comparison for `f`, then
the composition law `g^* ⋙ f^* ≅ (g ∘ f)^*` on complexes. -/
theorem derivedPullbackCompIso_hom_app_comp_pullbackComparisonQ
    (hmosf : f.u.IsMorphismOfSites Y.J X.J) (hmosg : g.u.IsMorphismOfSites Z.J Y.J)
    (M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ) :
    (derivedPullbackCompIso f g hmosf hmosg).hom.app (DerivedCategory.Q.obj M) ≫
        pullbackComparisonQ (g.comp f) M =
      (derivedPullback f).map (pullbackComparisonQ g M) ≫
        pullbackComparisonQ f ((pullbackComplex g).obj M) ≫
          DerivedCategory.Q.map ((pullbackComplexCompIso f g).hom.app M) := by
  simp only [pullbackComparisonQ_eq, derivedPullbackCompIso_hom]
  refine comp_of_three_factors (derivedPullback f) ?_
    (derivedPullbackCompComparison_app_comp_derivedPullbackComparison_app f g
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M)) ?_ ?_
  · exact ((derivedPullbackCompComparison f g).naturality
      ((DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))).inv.app M)).symm
  · exact pullbackOnHomotopyCompIso_hom_app_comp_quotientCompQhIso f g M
  · exact Iso.hom_inv_id_app _ _

end Main

end Stacks.Sheaves.DerivedPullback.CompositionLaw

end
