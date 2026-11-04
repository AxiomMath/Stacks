module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorComparisonMate

/-!
# The square isomorphism conjugating the counit, at a K-flat complex

`Dualizing.tensorComparisonCompatibility_of_homEquiv_square` reduces the obligation
`Dualizing.TensorComparisonCompatibility` to an equation whose only non-chain-level factor is

`γ.inv (Ff X|_R) ≫ baseChangeA (ε_{Ff X}) ≫ γ.hom X`,

the square isomorphism `Dualizing.derivedBaseChangeSquareIso` conjugating the counit of derived
extension of scalars along `R → A`.  The `γ.hom` is read at `X`, where
`Dualizing.derivedBaseChangeSquareIso_hom_app_q_obj` pins it down for a K-flat representative;
the `γ.inv` is read at `(Ff X)|_R`, and *that* complex is not K-flat over `R` for `X` the class
of a K-flat `K` — it is `(A ⊗_R K)|_R`, whose K-flatness over `R` is flatness of `A` over `R`.

This file shows that the conjugate is pinned down all the same, with no flatness of `A` and no
Tor independence: the square isomorphism's characterizing equation
`Dualizing.derivedBaseChangeSquareIso_hom_app_comp_comparison` does not have to be *inverted* at
`(A ⊗_R K)|_R`.  Read with `γ.inv` instead of `γ.hom` it says

`γ.inv (Q P) ≫ (comparison along R → A → A ⊗_R R') = (comparison along R → R' → A ⊗_R R')`

at *every* complex `P` of `R`-modules
(`Dualizing.derivedBaseChangeSquareIso_inv_app_comp_comparison`), and the counit factor that
follows `γ.inv` in the conjugate is, by
`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_counit_app_eq`, the model
comparison of `R → A` at `(A ⊗_R K)|_R` followed by the class of a *chain map* — the degreewise
counit `A ⊗_R (A ⊗_R K)|_R ⟶ A ⊗_R K`.  So the conjugate meets the characterizing equation at
`(A ⊗_R K)|_R` in the direction that needs no inverse, and the only invertibility used is the one
at `K` itself, which K-flatness of `K` supplies.

## Main results

* `Stacks.CategoryTheory.BaseChange.squareInv_comp_map_counit_comp_map` — the abstract step: for
  any morphism `a : Lf X ⟶ N` and any isomorphism `φ : Rf N ≅ P`, the square isomorphism's
  inverse at `Rf (Lf X)` followed by `Lg'` of the counit and `a` is `Lf' Lg` of
  `Rf a ≫ φ.hom`, the inverse at `P`, and `Lg'` of `Lf φ.inv ≫ counit`.  No adjunction mate and
  no invertibility of `a` enters: this is the naturality of the counit and of `γ.inv`.
* `Dualizing.derivedBaseChangeSquareIso_inv_app_comp_comparison` — the characterizing equation of
  the square isomorphism read with `γ.inv`: no invertibility of either composite comparison is
  needed for it.
* `Dualizing.squareIso_inv_counit_conjugate_app_q_obj` — **the conjugate at the class of a
  complex**, with `γ.inv` moved from `(A ⊗_R K)|_R` onto the class of `(A ⊗_R K)|_R` and the
  counit replaced by the model comparison and a chain map.  Still no hypothesis on `K`.
* `Dualizing.squareIso_inv_counit_conjugate_comp_comparisonA_app_q_obj` — the same, read against
  the model comparison of the `A → A ⊗_R R'` edge, where the chain map has become the class of its
  own degreewise extension of scalars.
* `Dualizing.compTailLeft` and `Dualizing.squareIso_counit_conjugate_comp_comparison_app_q_obj` —
  **the conjugate pinned**: composed with the composite comparison along `R → R' → A ⊗_R R'` at
  `K`, it is chain-level data and that same composite comparison at `(A ⊗_R K)|_R`.  The square
  isomorphism does not occur on the right-hand side, and the only hypotheses are the four
  derived-functor universal properties.

## Implementation notes

The abstract lemma is stated for a bare morphism `a`, not an isomorphism, so that the
instantiation can take `a` to be the model comparison `alphaf` at `K` without first producing its
invertibility; the only isomorphism it needs is
`CategoryTheory.Functor.mapDerivedCategoryFactors`, which is one for every functor.

The assembly is written as a forward chain of `Eq.trans` and `congrArg` rather than with `rw` or
`simp only [Category.assoc]`: the two spellings of the target of the composite comparison — the
one `Dualizing.compTailLeft` is declared with and the one the composite comparison of the
bottom-and-right edge carries — are definitionally equal but not syntactically, so keyed matching
does not cross them, and `rfl` across them diverges.  Every `Eq.trans` therefore has its *first*
argument known; a `refine Eq.trans ?_ h` whose `h` is a nested chain leaves the midpoint a
metavariable and times out at `whnf`.

No `@[stacks]` attribute is placed here: `Dualizing.TensorComparisonCompatibility` is still open,
so nothing in this file covers a tag.

## References

* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
* [Stacks Project, Tag 06Y1](https://stacks.math.columbia.edu/tag/06Y1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor StacksDraft.DerivedHom
open CochainComplex.DerivedExtensionScalars

namespace Stacks.CategoryTheory.BaseChange

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A : Type u₁} {B : Type u₂} {A' : Type u₃} {B' : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} A'] [Category.{v₄} B']
  {Lf : A ⥤ B} {Rf : B ⥤ A} {Lf' : A' ⥤ B'}
  {Lg : A ⥤ A'} {Lg' : B ⥤ B'}

/-- **The inverse square isomorphism conjugating a counit, moved onto another object.**  Let
`adjf : Lf ⊣ Rf`, let `γ : Lf ⋙ Lg' ≅ Lg ⋙ Lf'` and let `X` be an object of `A`.  For any
morphism `a : Lf X ⟶ N` and any isomorphism `φ : Rf N ≅ P`,

`γ.inv (Rf (Lf X)) ≫ Lg' (counit (Lf X) ≫ a)`

is `Lf' Lg` of `Rf a ≫ φ.hom`, then `γ.inv` at `P`, then `Lg'` of `Lf φ.inv ≫ counit N`.

Only two naturalities enter — that of the counit at `a` and that of `γ.inv` at `Rf a ≫ φ.hom` —
so neither an adjunction mate nor invertibility of `a` is needed.  The point of the statement is
that the object `γ.inv` is read at moves from `Rf (Lf X)`, where nothing is known about it, to
`P`, which the consumer chooses. -/
theorem squareInv_comp_map_counit_comp_map (adjf : Lf ⊣ Rf) (γ : Lf ⋙ Lg' ≅ Lg ⋙ Lf')
    (X : A) {N : B} (a : Lf.obj X ⟶ N) {P : A} (p : Rf.obj N ⟶ P) (q : P ⟶ Rf.obj N)
    (hpq : p ≫ q = 𝟙 (Rf.obj N)) :
    γ.inv.app (Rf.obj (Lf.obj X)) ≫ Lg'.map (adjf.counit.app (Lf.obj X) ≫ a) =
      Lf'.map (Lg.map (Rf.map a ≫ p)) ≫
        γ.inv.app P ≫ Lg'.map (Lf.map q ≫ adjf.counit.app N) := by
  have hnat : adjf.counit.app (Lf.obj X) ≫ a = Lf.map (Rf.map a) ≫ adjf.counit.app N := by
    have h := adjf.counit.naturality a
    dsimp only [Functor.comp_map, Functor.id_map] at h
    exact h.symm
  have hsplit : Lf.map (Rf.map a) ≫ adjf.counit.app N =
      Lf.map (Rf.map a ≫ p) ≫ Lf.map q ≫ adjf.counit.app N := by
    rw [← Category.assoc, ← Lf.map_comp, Category.assoc, hpq, Category.comp_id]
  have hγ := γ.inv.naturality (Rf.map a ≫ p)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hγ
  rw [hnat, hsplit, Lg'.map_comp, ← Category.assoc, ← hγ, Category.assoc]

end Stacks.CategoryTheory.BaseChange

namespace Dualizing

universe uR uA uRp v

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] extendScalarsAdditiveOfRingHom

variable {R : Type uR} {A : Type uA} {R' : Type uRp} [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']
  (hTor : RingTheory.TorIndependence.TorIndependent R A R')
  (baseChangeR :
    DerivedCategory (ModuleCat.{max v uR uA uRp} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} R'))
  (comparisonR :
    DerivedCategory.Q ⋙ baseChangeR ⟶
      (ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (baseChangeA :
    DerivedCategory (ModuleCat.{max v uR uA uRp} A) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} (TensorProduct R A R')))
  (comparisonA :
    DerivedCategory.Q ⋙ baseChangeA ⟶
      (ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
        (algebraMap A (TensorProduct R A R'))).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (Ff : DerivedCategory (ModuleCat.{max v uR uA uRp} R) ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp} A))
  (alphaf : DerivedCategory.Q ⋙ Ff ⟶
    (ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
      (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (Fi : DerivedCategory (ModuleCat.{max v uR uA uRp} R') ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp} (TensorProduct R A R')))
  (alphai : DerivedCategory.Q ⋙ Fi ⟶
    (ModuleCat.extendScalars.{uRp, max uA uRp, max v uR uA uRp}
      (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)

variable [hf : Ff.IsLeftDerivedFunctor alphaf
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ))]
  [hA : baseChangeA.IsLeftDerivedFunctor comparisonA
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} A) (ComplexShape.up ℤ))]
  [hR : baseChangeR.IsLeftDerivedFunctor comparisonR
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ))]
  [hi : Fi.IsLeftDerivedFunctor alphai
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R') (ComplexShape.up ℤ))]

include hf hA hR hi in
/-- **The characterizing equation of the base-change square isomorphism, read with `γ.inv`.**
`Dualizing.derivedBaseChangeSquareIso_hom_app_comp_comparison` says that `γ.hom` at the class of
`P` followed by the composite comparison along `R → R' → A ⊗_R R'` is the composite comparison
along `R → A → A ⊗_R R'`.  Cancelling `γ` on the left turns it into the statement that `γ.inv` at
the class of `P` followed by the composite comparison along `R → A → A ⊗_R R'` is the composite
comparison along `R → R' → A ⊗_R R'`.

This is the form that needs no invertibility: `Dualizing.derivedBaseChangeSquareIso_hom_app_q_obj`
has to invert the right-hand composite comparison at `P`, which only a K-flatness hypothesis on
`P` gives, whereas this holds at every `P`. -/
theorem derivedBaseChangeSquareIso_inv_app_comp_comparison
    (P : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ) :
    (derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR comparisonR
            Fi alphai).inv.app (DerivedCategory.Q.obj P) ≫
        (StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq.{uR, uA,
          max uA uRp, max v uRp, max v uR uA uRp + 1, max v uR uA uRp + 1,
          max v uR uA uRp + 1}
          (algebraMap R A) (algebraMap A (TensorProduct R A R'))
          Ff alphaf baseChangeA comparisonA
          (algebraMap R (TensorProduct R A R'))
          algebraMap_tensorProduct_comp_left).app P =
      (StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq.{uR, uRp,
        max uA uRp, max v uA, max v uR uA uRp + 1, max v uR uA uRp + 1,
        max v uR uA uRp + 1}
        (algebraMap R R')
        (Algebra.TensorProduct.includeRight :
          R' →ₐ[R] TensorProduct R A R').toRingHom
        baseChangeR comparisonR Fi alphai
        (algebraMap R (TensorProduct R A R'))
        algebraMap_tensorProduct_comp_right).app P := by
  rw [← derivedBaseChangeSquareIso_hom_app_comp_comparison Ff alphaf baseChangeA comparisonA
      baseChangeR comparisonR Fi alphai P, ← Category.assoc,
    Iso.inv_hom_id_app, Category.id_comp]

include hf hA hR hi in
/-- **The square isomorphism conjugating the counit, at the class of a complex.**  At `X` the
class of a cochain complex `K` of `R`-modules, the inverse square isomorphism at `(Ff X)|_R`
followed by the base change of the counit of derived extension of scalars along `R → A` at
`Ff X`, and by the model comparison `alphaf` at `K`, is:

* `Fi` of the base change along `R → R'` of the comparison `alphaf` at `K`, restricted to `R`
  and composed with the factorization of derived restriction of scalars — an explicit isomorphism
  `(Ff X)|_R ≅ Q ((A ⊗_R K)|_R)`;
* the inverse square isomorphism at the class of `(A ⊗_R K)|_R`;
* the base change of the model comparison at `(A ⊗_R K)|_R` and of the class of the degreewise
  counit `A ⊗_R (A ⊗_R K)|_R ⟶ A ⊗_R K`.

So the object the square isomorphism is read at has moved from `(Ff X)|_R`, about which nothing
is known, to the class of the complex `(A ⊗_R K)|_R`, and the counit has become a chain map.
Nothing is assumed about `K`: this is
`Stacks.CategoryTheory.BaseChange.squareInv_comp_map_counit_comp_map` with the counit formula
`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_counit_app_eq`. -/
theorem squareIso_inv_counit_conjugate_app_q_obj
    (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ) :
    (derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR comparisonR
            Fi alphai).inv.app
          ((ModuleCat.restrictScalars.{max v uR uA uRp}
            (algebraMap R A)).mapDerivedCategory.obj (Ff.obj (DerivedCategory.Q.obj K))) ≫
        baseChangeA.map
          ((derivedExtensionScalarsAdjunction.{uR, uA, max v uRp} (algebraMap R A) Ff
              alphaf).counit.app (Ff.obj (DerivedCategory.Q.obj K)) ≫ alphaf.app K) =
      Fi.map (baseChangeR.map
            ((ModuleCat.restrictScalars.{max v uR uA uRp}
                  (algebraMap R A)).mapDerivedCategory.map (alphaf.app K) ≫
              (ModuleCat.restrictScalars.{max v uR uA uRp}
                  (algebraMap R A)).mapDerivedCategoryFactors.hom.app
                (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
                  (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))) ≫
        (derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR comparisonR
              Fi alphai).inv.app
            (DerivedCategory.Q.obj
              (((ModuleCat.restrictScalars.{max v uR uA uRp}
                  (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
                  (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))) ≫
          baseChangeA.map
            (alphaf.app
                (((ModuleCat.restrictScalars.{max v uR uA uRp}
                    (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                  (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
                    (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
              DerivedCategory.Q.map
                (((ModuleCat.extendRestrictScalarsAdj.{max v uR uRp, uR, uA}
                    (algebraMap R A)).mapHomologicalComplex
                  (ComplexShape.up ℤ)).counit.app
                  (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
                    (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))) := by
  have key := Stacks.CategoryTheory.BaseChange.squareInv_comp_map_counit_comp_map
    (derivedExtensionScalarsAdjunction.{uR, uA, max v uRp} (algebraMap R A) Ff alphaf)
    (derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR comparisonR
      Fi alphai)
    (DerivedCategory.Q.obj K) (alphaf.app K)
    ((ModuleCat.restrictScalars.{max v uR uA uRp}
      (algebraMap R A)).mapDerivedCategoryFactors.hom.app
      (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
        (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
    ((ModuleCat.restrictScalars.{max v uR uA uRp}
      (algebraMap R A)).mapDerivedCategoryFactors.inv.app
      (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
        (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
    ((ModuleCat.restrictScalars.{max v uR uA uRp}
      (algebraMap R A)).mapDerivedCategoryFactors.hom_inv_id_app _)
  rw [key]
  dsimp only [Functor.comp_obj]
  rw [derivedExtensionScalarsAdjunction_counit_app.{uR, uA, max v uRp} (algebraMap R A)
    Ff alphaf
    (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
      (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)]

include hf hA hR hi in
/-- **The conjugate, read against the comparison of the `A → A ⊗_R R'` edge.**
`Dualizing.squareIso_inv_counit_conjugate_app_q_obj` followed by the model comparison
`comparisonA` at `A ⊗_R K`: the degreewise counit that the counit formula produced is a chain map
of complexes of `A`-modules, so the naturality of `comparisonA` carries it across, and what is
left of it is the class of its degreewise extension of scalars along `A → A ⊗_R R'`.

Everything to the right of `Fi (baseChangeR u)` is now either the square isomorphism at the class
of `(A ⊗_R K)|_R` — where
`Dualizing.derivedBaseChangeSquareIso_inv_app_comp_comparison` pins it against the composite
comparison, with no invertibility — or chain-level data.  Still no hypothesis on `K`. -/
theorem squareIso_inv_counit_conjugate_comp_comparisonA_app_q_obj
    (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ) :
    (derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR comparisonR
            Fi alphai).inv.app
          ((ModuleCat.restrictScalars.{max v uR uA uRp}
            (algebraMap R A)).mapDerivedCategory.obj (Ff.obj (DerivedCategory.Q.obj K))) ≫
        baseChangeA.map
            ((derivedExtensionScalarsAdjunction.{uR, uA, max v uRp} (algebraMap R A) Ff
                alphaf).counit.app (Ff.obj (DerivedCategory.Q.obj K)) ≫ alphaf.app K) ≫
          comparisonA.app
            (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
              (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
      Fi.map (baseChangeR.map
            ((ModuleCat.restrictScalars.{max v uR uA uRp}
                  (algebraMap R A)).mapDerivedCategory.map (alphaf.app K) ≫
              (ModuleCat.restrictScalars.{max v uR uA uRp}
                  (algebraMap R A)).mapDerivedCategoryFactors.hom.app
                (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
                  (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))) ≫
        (derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR comparisonR
                Fi alphai).inv.app
              (DerivedCategory.Q.obj
                (((ModuleCat.restrictScalars.{max v uR uA uRp}
                    (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                  (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
                    (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))) ≫
            baseChangeA.map
                (alphaf.app
                  (((ModuleCat.restrictScalars.{max v uR uA uRp}
                      (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                    (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
                      (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))) ≫
              comparisonA.app
                (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
                    (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                  (((ModuleCat.restrictScalars.{max v uR uA uRp}
                      (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                    (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
                      (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))) ≫
          DerivedCategory.Q.map
            (((ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
                  (algebraMap A (TensorProduct R A R'))).mapHomologicalComplex
                (ComplexShape.up ℤ)).map
              (((ModuleCat.extendRestrictScalarsAdj.{max v uR uRp, uR, uA}
                  (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).counit.app
                (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
                  (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))) := by
  have key := squareIso_inv_counit_conjugate_app_q_obj baseChangeR comparisonR baseChangeA
    comparisonA Ff alphaf Fi alphai K
  have hnat := comparisonA.naturality
    (((ModuleCat.extendRestrictScalarsAdj.{max v uR uRp, uR, uA}
        (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).counit.app
      (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
        (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hnat
  rw [← Category.assoc, key, Category.assoc, Category.assoc, baseChangeA.map_comp,
    Category.assoc, hnat]


/-- The degreewise composition isomorphism of the top-and-right edge `R → A → A ⊗_R R'`,
retargeted along `Dualizing.algebraMap_tensorProduct_comp_left`: the tail of the composite
comparison `StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq` of that edge. -/
def compTailLeft :
    (ModuleCat.extendScalars.{uR, uA, max v uR uA uRp} (algebraMap R A)).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        extensionOfScalarsComplexGeneral.{uA, max v uR uRp, max uA uRp,
          max v uR uA uRp + 1} (algebraMap A (TensorProduct R A R')) ≅
      extensionOfScalarsComplexGeneral.{uR, max v uA uRp, max uA uRp,
        max v uR uA uRp + 1} (algebraMap R (TensorProduct R A R')) :=
  StacksDraft.DerivedExtensionScalarsModelComp.extensionOfScalarsComplexCompIso.{uR, uA,
      max uA uRp, max v uRp, max v uR uA uRp + 1}
      (algebraMap R A) (algebraMap A (TensorProduct R A R')) ≪≫
    eqToIso (congrArg (fun φ => extensionOfScalarsComplexGeneral.{uR, max v uA uRp, max uA uRp,
      max v uR uA uRp + 1} φ) algebraMap_tensorProduct_comp_left)

omit hf hA in
/-- The composite comparison along `R → A → A ⊗_R R'`, factored: the model comparison of `R → A`,
the model comparison of `A → A ⊗_R R'` at the degreewise extension, and the tail
`Dualizing.compTailLeft`. -/
private theorem compComparisonOfEq_left_app
    (X : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ) :
    (StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq.{uR, uA,
        max uA uRp, max v uRp, max v uR uA uRp + 1, max v uR uA uRp + 1,
        max v uR uA uRp + 1}
        (algebraMap R A) (algebraMap A (TensorProduct R A R'))
        Ff alphaf baseChangeA comparisonA
        (algebraMap R (TensorProduct R A R'))
        algebraMap_tensorProduct_comp_left).app X =
      baseChangeA.map (alphaf.app X) ≫
        comparisonA.app
            (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
              (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ≫
          (compTailLeft.{uR, uA, uRp, v} (R := R) (A := A) (R' := R')).hom.app X := by
  dsimp only [StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq,
    NatTrans.comp_app, compTailLeft, Iso.trans_hom, eqToIso.hom]
  rw [StacksDraft.DerivedExtensionScalarsModelComp.compComparison_app.{uR, uA,
    max uA uRp, max v uRp, max v uR uA uRp + 1, max v uR uA uRp + 1, max v uR uA uRp + 1}
    (algebraMap R A) (algebraMap A (TensorProduct R A R')) Ff alphaf baseChangeA comparisonA X]
  exact (Category.assoc _ _ _).trans
    (congrArg (fun z => baseChangeA.map (alphaf.app X) ≫ z) (Category.assoc _ _ _))

/-- Reassociate a composite whose left factor is a right-nested composite of four morphisms. -/
private theorem assoc_four {C : Type*} [Category C] {W X Y Z V T : C} (a : W ⟶ X) (b : X ⟶ Y)
    (c : Y ⟶ Z) (d : Z ⟶ V) (e : V ⟶ T) : (a ≫ b ≫ c ≫ d) ≫ e = a ≫ b ≫ c ≫ d ≫ e := by
  simp only [Category.assoc]

include hf hA hR hi in
/-- **The square isomorphism conjugating the counit, pinned at the class of a K-flat complex.**
At `X = Q K` with `K` K-flat over `R`, the conjugate

`γ.inv ((Ff X)|_R) ≫ baseChangeA (ε_{Ff X}) ≫ γ.hom X`

— the only factor of `Dualizing.tensorComparisonCompatibility_of_homEquiv_square` that is not
chain-level — composed with the composite comparison along `R → R' → A ⊗_R R'` at `K`, is the
base change of the explicit isomorphism `(Ff X)|_R ≅ Q ((A ⊗_R K)|_R)`, the *same* composite
comparison at `(A ⊗_R K)|_R`, and the class of the degreewise counit extended along
`A → A ⊗_R R'`, conjugated by the composition isomorphism of the top-and-right edge.

No flatness of `A` over `R`, no Tor independence and no K-flatness of `(A ⊗_R K)|_R` enters, and
no hypothesis whatever is used on `K` here: the square isomorphism is read against the
characterizing equation at `(A ⊗_R K)|_R` in the direction
`Dualizing.derivedBaseChangeSquareIso_inv_app_comp_comparison`, which holds at every complex.
This is what `Dualizing.derivedBaseChangeSquareIso_hom_app_q_obj` could not deliver there: that
lemma has to *invert* the composite comparison at `(A ⊗_R K)|_R`, and `(A ⊗_R K)|_R` is not
K-flat over `R` unless `A` is flat over `R`. -/
theorem squareIso_counit_conjugate_comp_comparison_app_q_obj
    (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ) :
    ((derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR comparisonR
              Fi alphai).inv.app
            ((ModuleCat.restrictScalars.{max v uR uA uRp}
              (algebraMap R A)).mapDerivedCategory.obj (Ff.obj (DerivedCategory.Q.obj K))) ≫
          baseChangeA.map
              ((derivedExtensionScalarsAdjunction.{uR, uA, max v uRp} (algebraMap R A) Ff
                alphaf).counit.app (Ff.obj (DerivedCategory.Q.obj K))) ≫
            (derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR comparisonR
              Fi alphai).hom.app (DerivedCategory.Q.obj K)) ≫
        (StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq.{uR, uRp,
          max uA uRp, max v uA, max v uR uA uRp + 1, max v uR uA uRp + 1,
          max v uR uA uRp + 1}
          (algebraMap R R')
          (Algebra.TensorProduct.includeRight :
            R' →ₐ[R] TensorProduct R A R').toRingHom
          baseChangeR comparisonR Fi alphai
          (algebraMap R (TensorProduct R A R'))
          algebraMap_tensorProduct_comp_right).app K =
      Fi.map (baseChangeR.map
            ((ModuleCat.restrictScalars.{max v uR uA uRp}
                  (algebraMap R A)).mapDerivedCategory.map (alphaf.app K) ≫
              (ModuleCat.restrictScalars.{max v uR uA uRp}
                  (algebraMap R A)).mapDerivedCategoryFactors.hom.app
                (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
                  (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))) ≫
        (StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq.{uR, uRp,
              max uA uRp, max v uA, max v uR uA uRp + 1, max v uR uA uRp + 1,
              max v uR uA uRp + 1}
              (algebraMap R R')
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom
              baseChangeR comparisonR Fi alphai
              (algebraMap R (TensorProduct R A R'))
              algebraMap_tensorProduct_comp_right).app
            (((ModuleCat.restrictScalars.{max v uR uA uRp}
                (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
                (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
          (compTailLeft.{uR, uA, uRp, v} (R := R) (A := A) (R' := R')).inv.app
              (((ModuleCat.restrictScalars.{max v uR uA uRp}
                  (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
                  (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
            DerivedCategory.Q.map
                (((ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
                      (algebraMap A (TensorProduct R A R'))).mapHomologicalComplex
                    (ComplexShape.up ℤ)).map
                  (((ModuleCat.extendRestrictScalarsAdj.{max v uR uRp, uR, uA}
                      (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).counit.app
                    (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
                      (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))) ≫
              (compTailLeft.{uR, uA, uRp, v} (R := R) (A := A) (R' := R')).hom.app K := by
  have h3 := squareIso_inv_counit_conjugate_comp_comparisonA_app_q_obj baseChangeR comparisonR
    baseChangeA comparisonA Ff alphaf Fi alphai K
  have hhom := derivedBaseChangeSquareIso_hom_app_comp_comparison Ff alphaf baseChangeA
    comparisonA baseChangeR comparisonR Fi alphai K
  have hinv := derivedBaseChangeSquareIso_inv_app_comp_comparison baseChangeR comparisonR
    baseChangeA comparisonA Ff alphaf Fi alphai
    (((ModuleCat.restrictScalars.{max v uR uA uRp}
        (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
        (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
  rw [compComparisonOfEq_left_app baseChangeA comparisonA Ff alphaf
    (((ModuleCat.restrictScalars.{max v uR uA uRp}
        (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
        (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))] at hinv
  have hx : (StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq.{uR, uRp,
        max uA uRp, max v uA, max v uR uA uRp + 1, max v uR uA uRp + 1,
        max v uR uA uRp + 1}
        (algebraMap R R')
        (Algebra.TensorProduct.includeRight :
          R' →ₐ[R] TensorProduct R A R').toRingHom
        baseChangeR comparisonR Fi alphai
        (algebraMap R (TensorProduct R A R'))
        algebraMap_tensorProduct_comp_right).app
          (((ModuleCat.restrictScalars.{max v uR uA uRp}
              (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
              (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
        (compTailLeft.{uR, uA, uRp, v} (R := R) (A := A) (R' := R')).inv.app
          (((ModuleCat.restrictScalars.{max v uR uA uRp}
              (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
              (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) =
      (derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR comparisonR
            Fi alphai).inv.app
          (DerivedCategory.Q.obj
            (((ModuleCat.restrictScalars.{max v uR uA uRp}
                (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
                (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))) ≫
        baseChangeA.map
            (alphaf.app
              (((ModuleCat.restrictScalars.{max v uR uA uRp}
                  (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
                  (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))) ≫
          comparisonA.app
            (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
                (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              (((ModuleCat.restrictScalars.{max v uR uA uRp}
                  (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
                  (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))) := by
    refine Eq.trans (congrArg (· ≫ _) hinv).symm ?_
    refine Eq.trans (assoc_four _ _ _ _ _) ?_
    refine congrArg (_ ≫ ·) (congrArg (_ ≫ ·) ?_)
    exact Eq.trans (congrArg (_ ≫ ·)
      ((compTailLeft.{uR, uA, uRp, v} (R := R) (A := A) (R' := R')).hom_inv_id_app _))
      (Category.comp_id _)
  rw [baseChangeA.map_comp, Category.assoc] at h3
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (_ ≫ ·) (Category.assoc _ _ _)) ?_
  refine Eq.trans (congrArg (_ ≫ ·) (congrArg (_ ≫ ·) hhom)) ?_
  refine Eq.trans (congrArg (_ ≫ ·) (congrArg (_ ≫ ·)
    (compComparisonOfEq_left_app baseChangeA comparisonA Ff alphaf K))) ?_
  refine Eq.trans (assoc_four _ _ _ _ _).symm ?_
  refine Eq.trans (congrArg (· ≫ _) h3) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine congrArg (_ ≫ ·) ?_
  refine Eq.trans (assoc_four _ _ _ _ _) ?_
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine Eq.trans ?_ (congrArg (· ≫ _) hx.symm)
  exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _))).symm

end Dualizing

end
