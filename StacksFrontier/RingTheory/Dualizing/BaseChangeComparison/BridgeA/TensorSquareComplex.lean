module

public import StacksFrontier.Homology.ExtendScalars.Monoidal
public import StacksFrontier.Homology.HomComplex.Currying
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.BridgeA.Tensor
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.BridgeA.TensorSquare
import StacksFrontier.Homology.HomComplex.RHom.BaseChange
import all StacksFrontier.Homology.HomComplex.RHom.BaseChange.ProjectionFormula
import all StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.BridgeA.Tensor
import all StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.BridgeA.TensorSquare

/-!
# The projection formula at the two ring maps of a pushout square, on cochain complexes

Let

```
S --g--> T
|        |
p        w
v        v
S' --h-> T'
```

be a pushout square of commutative rings. The chain-level projection formula
`Dualizing.extendRestrictScalarsComplexIso` at `g`, base changed along `p`, is the same formula at
`h` read across the square, composed with the identification `S' ⊗_S T ≅ T'` in the tensor factor
and with the monoidality isomorphism `CochainComplex.ExtendScalars.extendScalarsMonoidalIso` of
degreewise extension of scalars. This is the cochain-complex form of the module-level statement
`Dualizing.extendRestrictScalarsModuleIso_square`.

The complex tensored with is concentrated in degree zero, so in degree `n` only the antidiagonal
summand of bidegree `(0, n)` of the total tensor product contributes, its Koszul sign is
`(-1)^(0 * n) = 1`, and the identity there is the module-level one.

## Main definitions

* `Dualizing.mapComplexCompIso`: degreewise application of a composite of two functors of module
  categories is the composite of the degreewise applications.
* `Dualizing.pushoutBaseChangeComplex`, `Dualizing.extendScalarsSquareIsoComplex`,
  `Dualizing.pushoutAlgebraIsoComplex`: the three comparisons of the square carried to cochain
  complexes.

## Main results

* `Stacks.CategoryTheory.eq_of_glued_factorizations`: two factorizations and two summand
  identities glue a five-factor composite to a two-factor one, in any category.
* `Stacks.CategoryTheory.comp_cancel_two`: the last two factors of a five-factor composite cancel
  against retractions of them, in any category.
* `Dualizing.extendRestrictScalarsComplexIso_hom_app_f`: the degreewise value of the chain-level
  projection formula: the module-level formula followed by the inclusion of the summand of
  bidegree `(0, n)`.
* `Dualizing.extendRestrictScalarsModuleIso_square_mu`: the module-level pairing written with the
  lax structure map of extension of scalars in place of the oplax one.
* `Dualizing.extendRestrictScalarsComplexIso_square`: **the chain-level pairing**, with the
  monoidality isomorphism of degreewise extension of scalars read forwards.
* `Dualizing.extendRestrictScalarsComplexIso_square_inv`: the same pairing in the orientation of
  `Dualizing.extendRestrictScalarsModuleIso_square`, with the oplax structure map on the left.

## References

* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
* [Stacks Project, Tag 0A6A](https://stacks.math.columbia.edu/tag/0A6A)
* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Functor
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal

universe u

namespace Stacks.CategoryTheory

/-- A morphism `lhs` which factors as `m ≫ i` agrees with a five-factor composite
`a ≫ b ≫ rhs₃ ≫ d ≫ e` as soon as

* `rhs₃` factors as `m' ≫ i'`,
* the second factor of that factorization absorbs `d` into a morphism `t` followed by `ii`,
* `ii` absorbs `e` into a morphism `mu` followed by the second factor `i` of `lhs`, and
* the first factor `m` of `lhs` is `a ≫ b ≫ m' ≫ t ≫ mu`. -/
theorem eq_of_glued_factorizations {C : Type*} [Category* C]
    {P Q₁ Q₂ R₁ R₂ R₃ R₄ W₁ W₂ : C}
    (lhs : P ⟶ Q₂) (m : P ⟶ Q₁) (i : Q₁ ⟶ Q₂) (hlhs : lhs = m ≫ i)
    (a : P ⟶ R₁) (b : R₁ ⟶ R₂)
    (rhs₃ : R₂ ⟶ R₄) (m' : R₂ ⟶ R₃) (i' : R₃ ⟶ R₄) (hrhs : rhs₃ = m' ≫ i')
    (d : R₄ ⟶ W₁) (e : W₁ ⟶ Q₂)
    (t : R₃ ⟶ W₂) (ii : W₂ ⟶ W₁) (hd : i' ≫ d = t ≫ ii)
    (mu : W₂ ⟶ Q₁) (he : ii ≫ e = mu ≫ i)
    (hm : m = a ≫ b ≫ m' ≫ t ≫ mu) :
    lhs = a ≫ b ≫ rhs₃ ≫ d ≫ e := by
  subst hlhs hrhs hm
  simp only [Category.assoc, reassoc_of% hd, he]

/-- A morphism `x` equal to `a ≫ b ≫ c ≫ d ≫ e`, followed by retractions `e'` of `e` and `d'` of
`d`, is `a ≫ b ≫ c`. -/
theorem comp_cancel_two {C : Type*} [Category* C] {P R₁ R₂ R₃ W₁ W₂ : C}
    (x : P ⟶ W₂) (a : P ⟶ R₁) (b : R₁ ⟶ R₂) (c : R₂ ⟶ R₃)
    (d : R₃ ⟶ W₁) (e : W₁ ⟶ W₂) (e' : W₂ ⟶ W₁) (d' : W₁ ⟶ R₃)
    (hx : x = a ≫ b ≫ c ≫ d ≫ e) (he : e ≫ e' = 𝟙 W₁) (hd : d ≫ d' = 𝟙 R₃) :
    x ≫ e' ≫ d' = a ≫ b ≫ c := by
  subst hx
  simp [reassoc_of% he, hd]

end Stacks.CategoryTheory

namespace Dualizing

variable {S T S' T' : Type u} [CommRing S] [CommRing T] [CommRing S'] [CommRing T']

/-- **The degreewise value of the chain-level projection formula.**  In degree `n` the component of
`Dualizing.extendRestrictScalarsComplexIso` at a complex `K` is the module-level projection formula
`Dualizing.extendRestrictScalarsModuleIso` at `K^n`, followed by the inclusion of the antidiagonal
summand of bidegree `(0, n)` of the total tensor product with the algebra placed in degree zero. -/
theorem extendRestrictScalarsComplexIso_hom_app_f (g : S →+* T)
    (K : CochainComplex (ModuleCat.{u} S) ℤ) (n : ℤ) :
    ((extendRestrictScalarsComplexIso g).hom.app K).f n =
      (extendRestrictScalarsModuleIso g).hom.app (K.X n) ≫
        HomologicalComplex.ιTensorObj
          ((CochainComplex.singleFunctor (ModuleCat.{u} S) 0).obj
            ((ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of T T))) K 0 n n (zero_add n) :=
  Stacks.DerivedHom.BaseChangeIso.extensionRestrictionComplexIso_hom_app_f g K n

/-- **Degreewise application of a composite is the composite of the degreewise applications.**  The
two functors `CochainComplex (ModuleCat X) ℤ ⥤ CochainComplex (ModuleCat Z) ℤ` obtained from
`F : ModuleCat X ⥤ ModuleCat Y` and `G : ModuleCat Y ⥤ ModuleCat Z` — apply `F ⋙ G` in each degree,
or apply `F` in each degree and then `G` in each degree — agree, componentwise by the identity.
This is `CategoryTheory.Functor.mapHomologicalComplexCompIso` at the identity of `F ⋙ G`. -/
def mapComplexCompIso {X Y Z : Type u} [CommRing X] [CommRing Y] [CommRing Z]
    (F : ModuleCat.{u} X ⥤ ModuleCat.{u} Y) (G : ModuleCat.{u} Y ⥤ ModuleCat.{u} Z)
    [F.Additive] [G.Additive] [(F ⋙ G).Additive] :
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        G.mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ) :=
  Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)

section Square

variable (g : S →+* T) (p : S →+* S') (w : T →+* T') (h : S' →+* T')
  (comm : w.comp g = h.comp p)

/-- **The pushout comparison of the square, on cochain complexes.**
`MilnorPatching.pushoutBaseChange` degreewise: extending along `w` and restricting along `h` is
restricting along `g` and extending along `p`, for a pushout square. -/
def pushoutBaseChangeComplex (hp : MilnorPatching.IsPushoutSquare g p w h comm) :
    (ModuleCat.extendScalars.{u, u, u} w).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (ModuleCat.restrictScalars.{u} h).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (ModuleCat.restrictScalars.{u} g).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (ModuleCat.extendScalars.{u, u, u} p).mapHomologicalComplex (ComplexShape.up ℤ) :=
  mapComplexCompIso (ModuleCat.extendScalars.{u, u, u} w) (ModuleCat.restrictScalars.{u} h) ≪≫
    NatIso.mapHomologicalComplex
      (MilnorPatching.pushoutBaseChange.{u} g p w h comm hp) (ComplexShape.up ℤ) ≪≫
    (mapComplexCompIso (ModuleCat.restrictScalars.{u} g)
      (ModuleCat.extendScalars.{u, u, u} p)).symm

/-- **The two extensions of scalars across the square agree, on cochain complexes.**
`Dualizing.extendScalarsSquareIso` degreewise. -/
def extendScalarsSquareIsoComplex :
    (ModuleCat.extendScalars.{u, u, u} p).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (ModuleCat.extendScalars.{u, u, u} h).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (ModuleCat.extendScalars.{u, u, u} g).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (ModuleCat.extendScalars.{u, u, u} w).mapHomologicalComplex (ComplexShape.up ℤ) :=
  mapComplexCompIso (ModuleCat.extendScalars.{u, u, u} p)
      (ModuleCat.extendScalars.{u, u, u} h) ≪≫
    NatIso.mapHomologicalComplex
      (extendScalarsSquareIso g p w h comm) (ComplexShape.up ℤ) ≪≫
    (mapComplexCompIso (ModuleCat.extendScalars.{u, u, u} g)
      (ModuleCat.extendScalars.{u, u, u} w)).symm

/-- **The lifted algebra of the square, in degree zero.**  The base change along `p` of the algebra
`T` placed in degree zero is the algebra `T'` placed in degree zero: the degreewise base change of
a complex concentrated in degree zero is concentrated in degree zero, and there
`Dualizing.pushoutAlgebraIso` identifies `S' ⊗_S T` with `T'`. -/
def pushoutAlgebraIsoComplex (hp : MilnorPatching.IsPushoutSquare g p w h comm) :
    ((ModuleCat.extendScalars.{u, u, u} p).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor (ModuleCat.{u} S) 0).obj
          ((ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of T T))) ≅
      (CochainComplex.singleFunctor (ModuleCat.{u} S') 0).obj
        ((ModuleCat.restrictScalars.{u} h).obj (ModuleCat.of T' T')) :=
  (HomologicalComplex.singleMapHomologicalComplex (ModuleCat.extendScalars.{u, u, u} p)
      (ComplexShape.up ℤ) 0).app ((ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of T T)) ≪≫
    (CochainComplex.singleFunctor (ModuleCat.{u} S') 0).mapIso
      (pushoutAlgebraIso g p w h comm hp)

/-- **The module-level pairing with the lax structure map.** The base change along `p` of the
projection formula at `g` is the pushout comparison, the identification of the two extensions of
scalars along the diagonal, the formula at `h`, the inverse of the lifted algebra in the tensor
factor, and the lax structure map `CategoryTheory.Functor.LaxMonoidal.μ` of extension of scalars
along `p`. This is `Dualizing.extendRestrictScalarsModuleIso_square`, which has the oplax
structure map `CategoryTheory.Functor.OplaxMonoidal.δ` and the lifted algebra on its left-hand
side instead. -/
theorem extendRestrictScalarsModuleIso_square_mu
    (hp : MilnorPatching.IsPushoutSquare g p w h comm) (M : ModuleCat.{u} S) :
    (ModuleCat.extendScalars.{u, u, u} p).map
        ((extendRestrictScalarsModuleIso g).hom.app M) =
      (MilnorPatching.pushoutBaseChange.{u} g p w h comm hp).inv.app
            ((ModuleCat.extendScalars.{u, u, u} g).obj M) ≫
          (ModuleCat.restrictScalars.{u} h).map
              ((extendScalarsSquareIso g p w h comm).inv.app M) ≫
            (extendRestrictScalarsModuleIso h).hom.app
                ((ModuleCat.extendScalars.{u, u, u} p).obj M) ≫
              ((pushoutAlgebraIso g p w h comm hp).inv ▷
                  ((ModuleCat.extendScalars.{u, u, u} p).obj M)) ≫
                μ (ModuleCat.extendScalars.{u, u, u} p)
                  ((ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of T T)) M := by
  have key := extendRestrictScalarsModuleIso_square g p w h comm hp M
  simp only [← Category.assoc] at key ⊢
  rw [← key]
  simp only [Category.assoc]
  rw [← MonoidalCategory.comp_whiskerRight_assoc, Iso.hom_inv_id,
    MonoidalCategory.id_whiskerRight, Category.id_comp, Functor.Monoidal.δ_μ]
  exact (Category.comp_id _).symm

/-- **The projection formula at the two ring maps of a pushout square, on cochain complexes.**  The
chain-level projection formula `Dualizing.extendRestrictScalarsComplexIso` at `g`, base changed
along `p`, is the same formula at `h` read across the square: the pushout comparison, the
identification of the two extensions of scalars along the diagonal, the formula at `h`, the lifted
algebra in the tensor factor, and the monoidality isomorphism
`CochainComplex.ExtendScalars.extendScalarsMonoidalIso` of degreewise extension of scalars. -/
theorem extendRestrictScalarsComplexIso_square
    (hp : MilnorPatching.IsPushoutSquare g p w h comm)
    (K : CochainComplex (ModuleCat.{u} S) ℤ) :
    ((ModuleCat.extendScalars.{u, u, u} p).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((extendRestrictScalarsComplexIso g).hom.app K) =
      (pushoutBaseChangeComplex g p w h comm hp).inv.app
            (((ModuleCat.extendScalars.{u, u, u} g).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K) ≫
          ((ModuleCat.restrictScalars.{u} h).mapHomologicalComplex (ComplexShape.up ℤ)).map
              ((extendScalarsSquareIsoComplex g p w h comm).inv.app K) ≫
            (extendRestrictScalarsComplexIso h).hom.app
              (((ModuleCat.extendScalars.{u, u, u} p).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K) ≫
              ((pushoutAlgebraIsoComplex g p w h comm hp).inv ▷
                  (((ModuleCat.extendScalars.{u, u, u} p).mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj K)) ≫
                (CochainComplex.ExtendScalars.extendScalarsMonoidalIso p
                  ((CochainComplex.singleFunctor (ModuleCat.{u} S) 0).obj
                    ((ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of T T))) K).hom := by
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  exact Stacks.CategoryTheory.eq_of_glued_factorizations _
    ((ModuleCat.extendScalars.{u, u, u} p).map
      ((extendRestrictScalarsModuleIso g).hom.app (K.X n)))
    ((ModuleCat.extendScalars.{u, u, u} p).map
      (HomologicalComplex.ιTensorObj
        ((CochainComplex.singleFunctor (ModuleCat.{u} S) 0).obj
          ((ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of T T))) K 0 n n (zero_add n)))
    (Eq.trans
      (congrArg (ModuleCat.extendScalars.{u, u, u} p).map
        (extendRestrictScalarsComplexIso_hom_app_f g K n))
      ((ModuleCat.extendScalars.{u, u, u} p).map_comp _ _))
    _ _ _
    ((extendRestrictScalarsModuleIso h).hom.app
      ((ModuleCat.extendScalars.{u, u, u} p).obj (K.X n)))
    (HomologicalComplex.ιTensorObj
      ((CochainComplex.singleFunctor (ModuleCat.{u} S') 0).obj
        ((ModuleCat.restrictScalars.{u} h).obj (ModuleCat.of T' T')))
      (((ModuleCat.extendScalars.{u, u, u} p).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) 0 n n (zero_add n))
    (extendRestrictScalarsComplexIso_hom_app_f h
      (((ModuleCat.extendScalars.{u, u, u} p).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) n)
    _ _
    ((pushoutAlgebraIso g p w h comm hp).inv ▷
      ((ModuleCat.extendScalars.{u, u, u} p).obj (K.X n)))
    (HomologicalComplex.ιTensorObj
      (((ModuleCat.extendScalars.{u, u, u} p).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor (ModuleCat.{u} S) 0).obj
          ((ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of T T))))
      (((ModuleCat.extendScalars.{u, u, u} p).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) 0 n n (zero_add n))
    (Stacks.HomComplex.Currying.ιTensorObj_comp_whiskerRight
      (L := ((ModuleCat.extendScalars.{u, u, u} p).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K)
      ((pushoutAlgebraIsoComplex g p w h comm hp).inv) (0 : ℤ) n n (zero_add n))
    (μ (ModuleCat.extendScalars.{u, u, u} p)
      ((ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of T T)) (K.X n))
    (CochainComplex.ExtendScalars.ι_extendScalarsMonoidalIso_hom p
      ((CochainComplex.singleFunctor (ModuleCat.{u} S) 0).obj
        ((ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of T T))) K n 0 n (zero_add n))
    (extendRestrictScalarsModuleIso_square_mu g p w h comm hp (K.X n))

/-- **The chain-level pairing in the shape of the module-level one.**
`Dualizing.extendRestrictScalarsComplexIso_square` read with the two invertible factors on the
left-hand side, which is the orientation of
`Dualizing.extendRestrictScalarsModuleIso_square`: the chain-level projection formula at `g` base
changed along `p`, the oplax structure map of degreewise extension of scalars, and the lifted
algebra in the tensor factor, against the formula at `h` read across the square. The oplax
structure map is the inverse of `CochainComplex.ExtendScalars.extendScalarsMonoidalIso`. -/
theorem extendRestrictScalarsComplexIso_square_inv
    (hp : MilnorPatching.IsPushoutSquare g p w h comm)
    (K : CochainComplex (ModuleCat.{u} S) ℤ) :
    ((ModuleCat.extendScalars.{u, u, u} p).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((extendRestrictScalarsComplexIso g).hom.app K) ≫
        (CochainComplex.ExtendScalars.extendScalarsMonoidalIso p
            ((CochainComplex.singleFunctor (ModuleCat.{u} S) 0).obj
              ((ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of T T))) K).inv ≫
          ((pushoutAlgebraIsoComplex g p w h comm hp).hom ▷
            (((ModuleCat.extendScalars.{u, u, u} p).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K)) =
      (pushoutBaseChangeComplex g p w h comm hp).inv.app
            (((ModuleCat.extendScalars.{u, u, u} g).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K) ≫
          ((ModuleCat.restrictScalars.{u} h).mapHomologicalComplex (ComplexShape.up ℤ)).map
              ((extendScalarsSquareIsoComplex g p w h comm).inv.app K) ≫
            (extendRestrictScalarsComplexIso h).hom.app
              (((ModuleCat.extendScalars.{u, u, u} p).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K) :=
  Stacks.CategoryTheory.comp_cancel_two _ _ _ _ _ _ _ _
    (extendRestrictScalarsComplexIso_square g p w h comm hp K)
    (Iso.hom_inv_id _)
    (by
      rw [← MonoidalCategory.comp_whiskerRight, Iso.inv_hom_id,
        MonoidalCategory.id_whiskerRight])

end Square

end Dualizing

end
