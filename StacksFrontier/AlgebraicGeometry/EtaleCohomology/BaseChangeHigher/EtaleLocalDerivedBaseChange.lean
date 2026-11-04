module

public import StacksFrontier.Algebra.Homology.HomotopyCategoryTransition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.EtaleLocality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.OrdinaryLocality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.OrdinaryLocalityCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.OpenClosedSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeHorizontalMate
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMate
public import StacksFrontier.RingTheory.Dualizing.DerivedHomBaseChange.Conservative

/-!
# The étale-local criterion for derived base change on small étale sites

Consider a cartesian square of schemes

```
X <--h-- Y
|f       |e
S <--g-- T
```

and an étale covering `{Uᵢ → X}` such that each `Uᵢ → S` factors as `Uᵢ → Vᵢ → S` with
`Vᵢ → S` étale.  Writing `Yᵢ = Uᵢ ×_X Y` and `Tᵢ = Vᵢ ×_S T`, the induced squares

```
Uᵢ <--hᵢ-- Yᵢ
|fᵢ        |eᵢ
Vᵢ <--gᵢ-- Tᵢ
```

are again cartesian.  This file carries out the argument of Stacks 0EZR for the base change map
on the **unbounded** derived category of abelian sheaves: if for every `i` the base change map
`fᵢ^{-1} Rg_{i,*} K|ᵢ ⟶ Rh_{i,*} eᵢ^{-1} K|ᵢ` of the `i`-th local square is an isomorphism, where
`K|ᵢ` is the inverse image of `K` along `Tᵢ ⟶ T`, then so is the base change map
`f^{-1} Rg_* K ⟶ Rh_* e^{-1} K` of the outer square.

## Main results

* `Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_isPullback_of_etale` — the appeal to
  Sites, Lemma 03EF: the **underived** comparison of a cartesian square whose two inverse-image
  legs are étale is invertible.
* `Stacks.EtaleCohomology.isIso_etaleAbelianDerivedBaseChange_of_isPullback_of_etale` — the same
  on the unbounded derived category, which is Cohomology on Sites, Lemma 0D6G for such a square.
* `Stacks.EtaleCohomology.isIso_etaleAbelianDerivedBaseChange_app_of_isIso_local` — **Stacks
  0EZR, part (2)**.

## Implementation notes

*The two étale squares.*  For the `i`-th upper and lower squares the comparison is invertible
for free.  Underived this is
`Stacks.EtaleCohomology.isIso_mate_smallEtaleSquarePushforwardIsoAt_of_isPullback`, which is
stated for an arbitrary pair of inverse-image/direct-image adjunctions; rewriting
`Stacks.EtaleCohomology.etaleAbelianBaseChange` as the horizontal mate of the comparison of the
two composite direct images,
`Stacks.EtaleCohomology.etaleAbelianBaseChange_eq_mateEquiv_symm_directImageCompIso`, puts the
two in the same shape, and `smallEtaleSquarePushforwardIsoAt_hom_eq_directImageCompIso'` matches
the two spellings of that comparison.

The passage from the underived statement to the derived one replays the argument of
`Stacks.EtaleCohomology.isIso_etaleAbelianDerivedBaseChange_of_isIso_etaleAbelianBaseChange`,
whose hypothesis that the two morphisms be integral is used there only to know that the
derived-functor units are invertible.  Here the morphisms are arbitrary, and the units are
instead invertible at a **K-injective** complex; that suffices, because every object of the
unbounded derived category is isomorphic to the class of a K-injective complex, and because the
inverse image along an étale morphism carries K-injective complexes to K-injective complexes —
being right adjoint to the exact extension by zero.

*The pasting.*  The rectangle `Uᵢ ⟶ X ⟶ S` is obtained in two ways: by stacking the outer square
on the `i`-th upper square, and by stacking the `i`-th local square on the `i`-th lower square,
the two being the same because `Uᵢ → X → S` is `Uᵢ → Vᵢ → S`.  Since
`Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange_comp_app` carries the two composite legs of
the rectangle as named morphisms, both presentations are instances of it, each expressing the
rectangle's comparison as a fourfold composite with two invertible outer factors.  The second
presentation shows the rectangle's comparison invertible; the first then shows the inverse image
along `Uᵢ` of the outer comparison invertible.

*Conservativity.*  Invertibility of a morphism of the unbounded derived category is detected on
cohomology, `DerivedCategory.isIso_iff`; the inverse image is exact, so cohomology commutes with
it, `CategoryTheory.Functor.mapDerivedCategoryCompHomologyFunctorIso`; and a morphism of abelian
sheaves whose inverse image to every member of an étale covering is invertible is invertible,
`Stacks.EtaleCohomology.isIso_of_isIso_etaleAbelianInverseImage_of_coversTop`, whose covering
hypothesis is `coversTop_smallEtaleObj_cover`.  Composing the three turns the conclusion of the
pasting step into the conclusion of the theorem.

## References

* [Stacks Project, Tag 0EZR](https://stacks.math.columbia.edu/tag/0EZR)
* [Stacks Project, Tag 03EF](https://stacks.math.columbia.edu/tag/03EF)
* [Stacks Project, Tag 0D6G](https://stacks.math.columbia.edu/tag/0D6G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

attribute [local instance] HasDerivedCategory.standard

universe u v z

namespace Stacks.EtaleCohomology

/-! ### The covering of Stacks 0EZR covers the final object -/

/-- **The members of the covering of Stacks 0EZR cover the final object of the small étale
site.**  The covering is an étale covering of `X` in the sense of
`AlgebraicGeometry.Scheme.etalePrecoverage`, that is, the images of its members cover the points
of `X`; that is exactly the condition for the sieve they generate on the final object of
`X_étale` to be covering, the final object being `X` over itself. -/
theorem coversTop_smallEtaleObj_cover {A : Type*} [Category* A]
    (D : EtaleLocalBaseChangeData.{u, z, _, _} A) (hEt : ∀ i, Etale (D.u i)) :
    D.X.smallEtaleTopology.CoversTop fun i => smallEtaleObj (D.u i) := by
  classical
  have (i : D.I) : Etale (D.u i) := hEt i
  let U : D.I → D.X.Etale := fun i => smallEtaleObj (D.u i)
  let top : D.X.Etale := smallEtaleObj (𝟙 D.X)
  have : IsIso top.hom := by
    rw [smallEtaleObj_hom]
    exact IsIso.id D.X
  let a : ∀ i, U i ⟶ top := fun i =>
    MorphismProperty.Over.homMk (D.u i) (Category.comp_id (D.u i)) trivial
  have htop : Sieve.ofArrows U a ∈ D.X.smallEtaleTopology top := by
    rw [ofArrows_mem_smallEtaleTopology_iff a]
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨i, y, rfl⟩ := ((Scheme.ofArrows_mem_precoverage_iff (@Etale)).mp D.cover).1 x
    exact Set.mem_iUnion.2 ⟨i, Set.mem_range.2 ⟨y, rfl⟩⟩
  exact (D.X.smallEtaleTopology.coversTop_iff_of_isTerminal top (isTerminalOfIsIsoHom top) U).2
    (D.X.smallEtaleTopology.superset_covering (Sieve.ofArrows_le_ofObjects U a) htop)

/-! ### Cancellation in a fourfold composite -/

/-- In a composite of four morphisms whose first, third and fourth factors are invertible, the
second factor is invertible.  This is the shape in which the pasting law for the derived base
change comparisons is used twice below; stated on variables, it costs nothing. -/
private theorem isIso_of_isIso_comp₄ {C : Type*} [Category* C] {A₀ A₁ A₂ A₃ A₄ : C}
    (a : A₀ ⟶ A₁) (m : A₁ ⟶ A₂) (b : A₂ ⟶ A₃) (c : A₃ ⟶ A₄)
    [IsIso a] [IsIso b] [IsIso c] (habc : IsIso (a ≫ m ≫ b ≫ c)) : IsIso m := by
  have := IsIso.of_isIso_comp_left a (m ≫ b ≫ c)
  exact IsIso.of_isIso_comp_right m (b ≫ c)

/-! ### The underived comparison of an étale cartesian square

The two developments spell the comparison of the two composite direct images around a square
differently: `Stacks.EtaleCohomology.smallEtaleSquarePushforwardIsoAt`, whose transport along the
commutativity of the square is an explicit `eqToIso`, and
`Stacks.EtaleCohomology.etaleAbelianDirectImageCompIso'`, which absorbs that transport into a
named composite.  The two lemmas below match them. -/

section UnderivedEtaleSquare

/-- The composition comparison for direct images with the composite carried as a named morphism,
read as the comparison for the written-out composite preceded by the transport along the equation
naming it. -/
private lemma etaleAbelianDirectImageCompIso'_inv_eq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) :
    (etaleAbelianDirectImageCompIso'.{u, v} f g fg hfg).inv =
      eqToHom (congrArg (fun k : X ⟶ Z => etaleAbelianDirectImage.{u, v} k) hfg) ≫
        (etaleAbelianDirectImageCompIso.{u, v} f g).inv := by
  subst hfg
  rw [etaleAbelianDirectImageCompIso'_rfl]
  simp

/-- **The two spellings of the comparison of the two composite direct images around a square
agree.**  The comparison used by the étale-locality development, whose transport along the
commutativity of the square is an explicit `eqToIso`, is the composite of the two named-composite
comparisons of the proper base change development. -/
private lemma smallEtaleSquarePushforwardIsoAt_hom_eq_directImageCompIso'
    {Y T X S : Scheme.{u}} (e : Y ⟶ T) (h : Y ⟶ X) (g : T ⟶ S) (f : X ⟶ S)
    (w : e ≫ g = h ≫ f) :
    (smallEtaleSquarePushforwardIsoAt e h g f w AddCommGrpCat.{max (u + 1) v}).hom =
      (etaleAbelianDirectImageCompIso'.{u, v} e g (e ≫ g) rfl).hom ≫
        (etaleAbelianDirectImageCompIso'.{u, v} h f (e ≫ g) w).inv := by
  rw [etaleAbelianDirectImageCompIso'_inv_eq.{u, v} h f (e ≫ g) w,
    etaleAbelianDirectImageCompIso'_rfl]
  rfl

/-- **The underived base change comparison of a cartesian square whose two inverse-image legs are
étale is invertible.**  For a cartesian square

```
T' --t--> T
|g'       |g
S' --p--> S
```

of schemes with `p` and `t` étale, the comparison `p^{-1} g_* ⟶ g'_* t^{-1}` of
`Stacks.EtaleCohomology.etaleAbelianBaseChange` is an isomorphism of functors on abelian sheaves
of the small étale sites.

This is the appeal to Sites, Lemma 03EF in the proof of Stacks 0EZR.  Both the comparison here
and the one of `Stacks.EtaleCohomology.isIso_mate_smallEtaleSquarePushforwardIsoAt_of_isPullback`
are mates of the comparison of the two composite direct images around the square, so no geometry
is left to do: on sections that comparison is the canonical identification of two presentations
of one fibre product. -/
theorem isIso_etaleAbelianBaseChange_of_isPullback_of_etale {S S' T T' : Scheme.{u}}
    (g : T ⟶ S) (p : S' ⟶ S) (t : T' ⟶ T) (g' : T' ⟶ S') [Etale p] [Etale t]
    (sq : IsPullback t g' g p) (w : t ≫ g = g' ≫ p) :
    IsIso (etaleAbelianBaseChange.{u, v} g p t g' w) := by
  have hall : ∀ F, IsIso ((etaleAbelianBaseChange.{u, v} g p t g' w).app F) := by
    intro F
    have hmate := isIso_mate_smallEtaleSquarePushforwardIsoAt_of_isPullback
      AddCommGrpCat.{max (u + 1) v} t g' g p w sq
      (etaleAbelianInverseImageDirectImageAdj.{u, v} t)
      (etaleAbelianInverseImageDirectImageAdj.{u, v} p) F
    rw [smallEtaleSquarePushforwardIsoAt_hom_eq_directImageCompIso'.{u, v} t g' g p w]
      at hmate
    rwa [etaleAbelianBaseChange_eq_mateEquiv_symm_directImageCompIso.{u, v} g p t g' w
      (t ≫ g) rfl w]
  exact NatIso.isIso_of_isIso_app _

end UnderivedEtaleSquare

/-! ### K-injectivity along an étale morphism, and the derived-functor units -/

section KInjective

/-- **The inverse image along an étale morphism carries K-injective complexes to K-injective
complexes.**  Along an étale morphism the inverse image is restriction, whose left adjoint is
extension by zero, and extension by zero is exact. -/
private theorem isKInjective_mapHomologicalComplex_etaleAbelianInverseImage
    {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
    (I : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ)
    [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((etaleAbelianInverseImage.{u, v} j).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) := by
  have hres : CochainComplex.IsKInjective
      (((etaleRestriction.{u, v} j).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
    CochainComplex.isKInjective_mapHomologicalComplex_of_exact
      (etaleRestriction.{u, v} j) (extensionByZero.{u, v} j) (extensionByZeroAdj.{u, v} j) I
  exact CochainComplex.isKInjective_of_iso
    ((NatIso.mapHomologicalComplex (etaleAbelianInverseImageRestrictionIso.{u, v} j)
      (ComplexShape.up ℤ)).app I).symm

/-- **The derived-functor unit of `Rf_*` is invertible at a K-injective complex.**  No hypothesis
on `f` is needed: this is the defining property of a right derived functor computed by
K-injective resolutions. -/
private theorem isIso_etaleAbelianDerivedDirectImageUnit_app_quotient {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    (I : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ)
    [I.IsKInjective] :
    IsIso ((etaleAbelianDerivedDirectImageUnit.{u, v} f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    (etaleAbelianPushforwardToDerivedCategory.{u, v} f)
    Stacks.DerivedFunctor.exists_quasiIso_isKInjective).2
    DerivedCategory.Qh _ _ I inferInstance

/-- **Every object of the unbounded derived category of abelian sheaves on a small étale site is
isomorphic to the class of a K-injective complex.**  Such sheaves form a Grothendieck abelian
category, so every complex admits a K-injective resolution by Stacks 079P. -/
private theorem exists_isKInjective_qh_iso (X : Scheme.{u})
    (Z : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})) :
    ∃ I : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ,
      I.IsKInjective ∧
        Nonempty (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I) ≅ Z) := by
  obtain ⟨I, q, hI, hq⟩ :=
    Stacks.DerivedFunctor.exists_quasiIso_isKInjective (DerivedCategory.Q.objPreimage Z)
  refine ⟨I, hI, ⟨?_⟩⟩
  have hiso : IsIso (DerivedCategory.Q.map q) :=
    Localization.inverts DerivedCategory.Q (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) q hq
  exact (DerivedCategory.quotientCompQhIso _).app I ≪≫
    (asIso (DerivedCategory.Q.map q)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso Z

end KInjective

/-! ### From the underived comparison to the derived one, without an integrality hypothesis -/

section UnderivedToDerived

variable {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (hyp : g' ≫ f = f' ≫ g)

/-- The degreewise base change comparison on homotopy categories is invertible as soon as the
underived comparison is. -/
private theorem isIso_etaleAbelianHomotopyBaseChange_of_isIso
    (hbc : IsIso (etaleAbelianBaseChange.{u, v} f g g' f' hyp)) :
    IsIso (etaleAbelianHomotopyBaseChange.{u, v} f g g' f' hyp) := by
  have : IsIso (NatTrans.mapHomotopyCategory (etaleAbelianBaseChange.{u, v} f g g' f' hyp)
      (ComplexShape.up ℤ)) :=
    CategoryTheory.isIso_natTrans_mapHomotopyCategory _ _
  rw [etaleAbelianHomotopyBaseChange]
  infer_instance

/-- **The derived base change comparison is invertible at the class of a complex at which both
derived-functor units are invertible**, provided the underived comparison is invertible.  This is
the proof of
`Stacks.EtaleCohomology.isIso_etaleAbelianDerivedBaseChange_of_isIso_etaleAbelianBaseChange` with
the invertibility of the two units turned from a consequence of integrality into a hypothesis. -/
private theorem isIso_etaleAbelianDerivedBaseChange_app_quotient
    (I : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ)
    (hu : IsIso ((etaleAbelianDerivedDirectImageUnit.{u, v} f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)))
    (hu' : IsIso ((etaleAbelianDerivedDirectImageUnit.{u, v} f').app
      (((etaleAbelianInverseImage.{u, v} g').mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))))
    (hbc : IsIso (etaleAbelianBaseChange.{u, v} f g g' f' hyp)) :
    IsIso ((etaleAbelianDerivedBaseChange.{u, v} f g g' f' hyp).app
      (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) := by
  set K := (HomotopyCategory.quotient
    (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (ComplexShape.up ℤ)).obj I
  have h₃ : IsIso (etaleAbelianHomotopyBaseChange.{u, v} f g g' f' hyp) :=
    isIso_etaleAbelianHomotopyBaseChange_of_isIso.{u, v} f g g' f' hyp hbc
  have hrw : (etaleAbelianDerivedBaseChange.{u, v} f g g' f' hyp).app
        (DerivedCategory.Qh.obj K) =
      inv ((etaleAbelianDerivedInverseImage.{u, v} g).map
          ((etaleAbelianDerivedDirectImageUnit.{u, v} f).app K)) ≫
        inv ((etaleAbelianInverseImage.{u, v} g).mapDerivedCategoryFactorsh.inv.app
          (((etaleAbelianDirectImage.{u, v} f).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj K)) ≫
        (DerivedCategory.Qh.map ((etaleAbelianHomotopyBaseChange.{u, v} f g g' f' hyp).app K) ≫
          (etaleAbelianDerivedDirectImageUnit.{u, v} f').app
            (((etaleAbelianInverseImage.{u, v} g').mapHomotopyCategory
              (ComplexShape.up ℤ)).obj K) ≫
          (etaleAbelianDerivedDirectImage.{u, v} f').map
            ((etaleAbelianInverseImage.{u, v} g').mapDerivedCategoryFactorsh.inv.app K)) := by
    rw [← etaleAbelianDerivedBaseChange_fac.{u, v} f g g' f' hyp K]
    simp
  rw [hrw]
  infer_instance

/-- **The derived base change comparison of a cartesian square whose two inverse-image legs are
étale is invertible**, on the whole unbounded derived category.  For a cartesian square

```
T' --t--> T
|g'       |g
S' --p--> S
```

of schemes with `p` and `t` étale, the base change map `p^{-1} Rg_* ⟶ Rg'_* t^{-1}` of
`Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange` is an isomorphism; no boundedness or
torsion condition is imposed, and nothing is assumed of `g`.

This is Cohomology on Sites, Lemma 0D6G for such a square, in the form the proof of Stacks 0EZR
uses it.  The underived comparison is invertible by
`isIso_etaleAbelianBaseChange_of_isPullback_of_etale`, and the passage to the unbounded derived
category is by K-injective resolutions: the derived-functor units of `Rg_*` and `Rg'_*` are
invertible at a K-injective complex and at its inverse image along `t`, which is K-injective
because `t` is étale. -/
theorem isIso_etaleAbelianDerivedBaseChange_of_isPullback_of_etale {S S' T T' : Scheme.{u}}
    (g : T ⟶ S) (p : S' ⟶ S) (t : T' ⟶ T) (g' : T' ⟶ S') [Etale p] [Etale t]
    (sq : IsPullback t g' g p) (w : t ≫ g = g' ≫ p) :
    IsIso (etaleAbelianDerivedBaseChange.{u, v} g p t g' w) := by
  have hall : ∀ Z, IsIso ((etaleAbelianDerivedBaseChange.{u, v} g p t g' w).app Z) := by
    intro Z
    obtain ⟨I, hI, ⟨eZ⟩⟩ := exists_isKInjective_qh_iso.{u, v} T Z
    have hIt : CochainComplex.IsKInjective
        (((etaleAbelianInverseImage.{u, v} t).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) :=
      isKInjective_mapHomologicalComplex_etaleAbelianInverseImage.{u, v} t I
    have hu' : IsIso ((etaleAbelianDerivedDirectImageUnit.{u, v} g').app
        (((etaleAbelianInverseImage.{u, v} t).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) :=
      (NatTrans.isIso_app_iff_of_iso (etaleAbelianDerivedDirectImageUnit.{u, v} g')
        (((etaleAbelianInverseImage.{u, v} t).mapHomotopyCategoryFactors
          (ComplexShape.up ℤ)).app I)).mpr
        (isIso_etaleAbelianDerivedDirectImageUnit_app_quotient.{u, v} g'
          (((etaleAbelianInverseImage.{u, v} t).mapHomologicalComplex (ComplexShape.up ℤ)).obj I))
    exact (NatTrans.isIso_app_iff_of_iso (etaleAbelianDerivedBaseChange.{u, v} g p t g' w) eZ).mp
      (isIso_etaleAbelianDerivedBaseChange_app_quotient.{u, v} g p t g' w I
        (isIso_etaleAbelianDerivedDirectImageUnit_app_quotient.{u, v} g I) hu'
        (isIso_etaleAbelianBaseChange_of_isPullback_of_etale.{u, v} g p t g' sq w))
  exact NatIso.isIso_of_isIso_app _

end UnderivedToDerived

/-! ### The two decompositions of the rectangle `Uᵢ ⟶ X ⟶ S` -/

section Pasting

/-- The rectangle `Uᵢ ⟶ X ⟶ S` of Stacks 0EZR commutes: both of its presentations have the same
two composite legs. -/
private lemma rectangle_comm (D : EtaleLocalBaseChangeData.{u, z, _, _} Ab.{u + 1}) (i : D.I) :
    (D.toY_i i ≫ D.e) ≫ D.g = D.h_i i ≫ (D.u i ≫ D.f) := by
  rw [Category.assoc, ← D.cartesian.w, reassoc_of% (D.upper_cartesian i).w]

/-- **The inverse image to `Uᵢ` of the outer comparison is invertible.**  Both decompositions of
the rectangle `Uᵢ ⟶ X ⟶ S` express the comparison attached to it as a fourfold composite whose
first and last factors are invertible.  In the decomposition through the `i`-th lower square the
remaining two factors are the inverse image of the lower square's comparison — invertible because
that square is cartesian with both inverse-image legs étale — and the `i`-th local square's
comparison, which is the hypothesis; so the rectangle's comparison is invertible.  In the
decomposition through the outer square the remaining two factors are the inverse image of the
outer comparison and the `i`-th upper square's comparison, again invertible for being attached to
a cartesian square with both inverse-image legs étale; cancelling the three invertible factors
leaves the first. -/
private theorem isIso_etaleAbelianDerivedInverseImage_map_app
    (D : EtaleLocalBaseChangeData.{u, z, _, _} Ab.{u + 1})
    (K : DerivedCategory (Sheaf D.T.smallEtaleTopology Ab.{u + 1})) (i : D.I)
    (hEt : Etale (D.u i))
    (hloc : IsIso ((etaleAbelianDerivedBaseChange.{u, 0} (D.g_i i) (D.f_i i) (D.e_i i)
      (D.h_i i) (D.local_cartesian i).w.symm).app
        ((etaleAbelianDerivedInverseImage.{u, 0} (D.toT_i i)).obj K))) :
    IsIso ((etaleAbelianDerivedInverseImage.{u, 0} (D.u i)).map
      ((etaleAbelianDerivedBaseChange.{u, 0} D.g D.f D.e D.h D.cartesian.w.symm).app K)) := by
  have hv : Etale (D.v i) := D.etale_v i
  have hY : Etale (D.toY_i i) := Etale.etale_of_isPullback_snd (D.upper_cartesian i)
  have hT : Etale (D.toT_i i) := Etale.etale_of_isPullback_snd (D.lower_cartesian i)
  have hyp := rectangle_comm D i
  have hA := etaleAbelianDerivedBaseChange_comp_app.{u, 0} D.f D.g D.h D.e (D.u i) (D.h_i i)
    (D.toY_i i) D.cartesian.w.symm (D.upper_cartesian i).w.symm
    (D.u i ≫ D.f) rfl (D.toY_i i ≫ D.e) rfl hyp K
  have hB := etaleAbelianDerivedBaseChange_comp_app.{u, 0} (D.v i) D.g (D.g_i i) (D.toT_i i)
    (D.f_i i) (D.h_i i) (D.e_i i) (D.lower_cartesian i).w.symm (D.local_cartesian i).w.symm
    (D.u i ≫ D.f) (D.factorization i).symm (D.toY_i i ≫ D.e) (D.e_i_compatible i).symm hyp K
  have := isIso_etaleAbelianDerivedBaseChange_of_isPullback_of_etale.{u, 0}
    D.g (D.v i) (D.toT_i i) (D.g_i i) (D.lower_cartesian i).flip (D.lower_cartesian i).w.symm
  have := isIso_etaleAbelianDerivedBaseChange_of_isPullback_of_etale.{u, 0}
    D.h (D.u i) (D.toY_i i) (D.h_i i) (D.upper_cartesian i).flip (D.upper_cartesian i).w.symm
  have hrect : IsIso ((etaleAbelianDerivedBaseChange.{u, 0} D.g (D.u i ≫ D.f)
      (D.toY_i i ≫ D.e) (D.h_i i) hyp).app K) := by
    rw [hB]
    infer_instance
  rw [hA] at hrect
  exact isIso_of_isIso_comp₄ _ _ _ _ hrect

end Pasting

/-! ### Stacks 0EZR, part (2) -/

section DerivedLocal

/-- **A morphism of the unbounded derived category which becomes invertible on every member of
the covering of Stacks 0EZR is invertible.**  Invertibility is detected on cohomology, the
inverse image is exact so commutes with cohomology, and invertibility of a morphism of abelian
sheaves on the small étale site is local. -/
private theorem isIso_of_isIso_etaleAbelianDerivedInverseImage
    (D : EtaleLocalBaseChangeData.{u, z, _, _} Ab.{u + 1}) (hEt : ∀ i, Etale (D.u i))
    {P Q : DerivedCategory (Sheaf D.X.smallEtaleTopology Ab.{u + 1})} (φ : P ⟶ Q)
    (h : ∀ i, IsIso ((etaleAbelianDerivedInverseImage.{u, 0} (D.u i)).map φ)) : IsIso φ := by
  have hEt' (i : D.I) : Etale (D.u i) := hEt i
  rw [DerivedCategory.isIso_iff]
  intro n
  refine isIso_of_isIso_etaleAbelianInverseImage_of_coversTop.{u, 0, z}
    ((DerivedCategory.homologyFunctor
      (Sheaf D.X.smallEtaleTopology Ab.{u + 1}) n).map φ) D.u
    (coversTop_smallEtaleObj_cover D hEt) fun i => ?_
  have hi : IsIso (((etaleAbelianInverseImage.{u, 0} (D.u i)).mapDerivedCategory ⋙
      DerivedCategory.homologyFunctor _ n).map φ) := by
    have := h i
    exact inferInstanceAs (IsIso ((DerivedCategory.homologyFunctor
      (Sheaf (D.U i).smallEtaleTopology Ab.{u + 1}) n).map
        ((etaleAbelianDerivedInverseImage.{u, 0} (D.u i)).map φ)))
  exact (NatIso.isIso_map_iff
    ((etaleAbelianInverseImage.{u, 0} (D.u i)).mapDerivedCategoryCompHomologyFunctorIso n)
    φ).mp hi

/-- **Stacks 0EZR, part (2).**  Let

```
X <--h-- Y
|f       |e
S <--g-- T
```

be a cartesian square of schemes, let `{Uᵢ → X}` be an étale covering of `X` such that each
composite `Uᵢ → X → S` factors as `Uᵢ → Vᵢ → S` with `Vᵢ → S` étale, let

```
Uᵢ <--hᵢ-- Yᵢ
|fᵢ        |eᵢ
Vᵢ <--gᵢ-- Tᵢ
```

be the induced cartesian squares, with `Yᵢ = Uᵢ ×_X Y` and `Tᵢ = Vᵢ ×_S T`, and let `K` be an
object of the unbounded derived category of abelian sheaves on the small étale site of `T`.  If
for every `i` the base change map `fᵢ^{-1} Rg_{i,*} K|ᵢ ⟶ Rh_{i,*} eᵢ^{-1} K|ᵢ` of the `i`-th
local square is an isomorphism, where `K|ᵢ` is the inverse image of `K` along `Tᵢ ⟶ T`, then the
base change map `f^{-1} Rg_* K ⟶ Rh_* e^{-1} K` of the outer square is an isomorphism.

The hypotheses are exactly the source's; nothing is assumed of `f`, `g`, `h`, `e` beyond the
square being cartesian, and `K` is an arbitrary object of the unbounded derived category, with no
boundedness or torsion condition.

The argument is the source's.  Over each `Uᵢ` the inverse image of the outer base change map is
compared with the base change map of the `i`-th local square through the pasting law for the
derived base change comparisons: the rectangle `Uᵢ ⟶ X ⟶ S` is obtained both by stacking the
outer square on the `i`-th upper square and by stacking the `i`-th local square on the `i`-th
lower square.  The base change maps of the upper and lower squares are invertible because those
squares are cartesian with both inverse-image legs étale, which is
`isIso_etaleAbelianDerivedBaseChange_of_isPullback_of_etale` — the appeal to Sites, Lemma 03EF
and Cohomology on Sites, Lemma 0D6G in the source.  Invertibility of the inverse image of a
morphism of the derived category over every member of the covering gives invertibility, because
invertibility is detected on cohomology and is local on the small étale site. -/
theorem isIso_etaleAbelianDerivedBaseChange_app_of_isIso_local
    (D : EtaleLocalBaseChangeData.{u, z, _, _} Ab.{u + 1})
    (K : DerivedCategory (Sheaf D.T.smallEtaleTopology Ab.{u + 1}))
    (hlocal : ∀ i : D.I,
      IsIso ((etaleAbelianDerivedBaseChange.{u, 0} (D.g_i i) (D.f_i i) (D.e_i i) (D.h_i i)
        (D.local_cartesian i).w.symm).app
          ((etaleAbelianDerivedInverseImage.{u, 0} (D.toT_i i)).obj K))) :
    IsIso ((etaleAbelianDerivedBaseChange.{u, 0} D.g D.f D.e D.h D.cartesian.w.symm).app K) := by
  have hEt : ∀ i, Etale (D.u i) := ((Scheme.ofArrows_mem_precoverage_iff (@Etale)).mp D.cover).2
  exact isIso_of_isIso_etaleAbelianDerivedInverseImage D hEt _
    fun i => isIso_etaleAbelianDerivedInverseImage_map_app D K i (hEt i) (hlocal i)

end DerivedLocal

end Stacks.EtaleCohomology

end
