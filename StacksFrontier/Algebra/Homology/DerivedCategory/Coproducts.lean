module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.CategoryTheory.Localization.FiniteProducts
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedLimits
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Countable direct sums in the derived category

Let `A` be an abelian category with *exact countable direct sums*: countable coproducts exist in
`A` and, for every countable index set `J`, the direct sum functor `colim : (Discrete J ⥤ A) ⥤ A`
is exact. Then the derived category `D(A)` has countable direct sums, and they are computed by
termwise direct sums of complexes: for a countable family `K : J → CochainComplex A ℤ`, the
coproduct `∐ K` in `CochainComplex A ℤ` — the complex `n ↦ ∐ⱼ (K j)ⁿ` — together with the images
`Q (ιⱼ)` of the canonical injections, is a direct sum of the family `(Q (K j))ⱼ` in `D(A)`.
Equivalently, `Q : C(A) ⥤ D(A)` preserves countable coproducts.

The proof is the source's, in four steps. The homotopy quotient `C(A) ⥤ K(A)` is additive, full
and the identity on objects, so it carries the termwise direct-sum cofan to a coproduct cofan in
`K(A)`: a map out of `∐ K` is a family of maps out of the `K j`, and a family of homotopies
between the legs assembles degreewise into a homotopy, because `∐ K` is computed degreewise. In
particular `K(A)` has countable direct sums. Next, `Hⁿ` commutes with countable direct sums —
this, and only this, is where exactness of `colim` is used — so quasi-isomorphisms in `K(A)` are
stable under countable direct sums. Finally, a localization at a morphism property stable under
`J`-coproducts preserves `J`-coproducts; applied to `Qh : K(A) ⥤ D(A)` and combined with
`Q = quotient ⋙ Qh`, that is the lemma.

## Main definitions

* `HasExactCountableDirectSums`: countable direct sums exist in `A` and are exact.

## Main results

* `derivedCategory_Q_preservesCoproductsOfShape`: `Q : C(A) ⥤ D(A)` preserves countable
  coproducts.
* `derivedCategory_termwiseDirectSum_isColimit`: the termwise direct sum of a countable family of
  complexes, with its canonical injections, is a direct sum in `D(A)`.
* `derivedCategory_hasCountableCoproducts`: `D(A)` has countable direct sums.
* `derivedCategory_Q_preservesCoproductsOfShape_of_enoughInjectives`: if instead `A` has enough
  injectives and exact countable products, then `Q` preserves coproducts of *every* shape
  available in `A`.

## Implementation notes

Mathlib has the last step only for finite index sets and only on the product side
(`Localization.preservesProductsOfShape`, whose sole use of finiteness is
`Functor.IsLocalization.pi`). Both restrictions are lifted here.
`functor_pi_isLocalization_of_hasLeftCalculusOfFractions` proves that a product of localizations
is a localization for an arbitrary index type, provided the morphism properties admit a left
calculus of fractions: the Hom-sets of the product localization are described by *product* left
fractions, assembled componentwise, so no infinite product is asked to commute with a filtered
colimit. `localization_preservesCoproductsOfShape` is then the colimit dual of Mathlib's lemma,
resting on the `Cocone` duals of `coneOfAdj`/`isLimitConeOfAdj` gathered in `ColimAux`.

`HasExactCountableDirectSums` bundles the hypothesis of the lemma as a `Prop`-valued structure,
quantified over all countable index types, and is passed explicitly rather than found by instance
search. Exactness of the direct sum functor is recorded as preservation of finite limits *and* of
finite colimits; the second half is automatic, `colim` being a left adjoint, but both are what its
consumers ask for.

The index type `J` of the countable statement is in `Type 0`, which is no restriction on a
countable type; the objects and morphisms of `A`, and the morphisms of `D(A)`, live in arbitrary
universes. The homotopy-category half of the argument (`HomotopyCategoryCoproduct`) uses neither
countability nor exactness, so it is stated for an index type in an arbitrary universe and is
shared with the K-injective route of the last section.

## References

* [Stacks Project, Tag 0A5L](https://stacks.math.columbia.edu/tag/0A5L) (Lemma 13.33.5).
-/

@[expose] public section

-- Works around the isDefEq-transparency change in this Lean bump: numerous `rw`/`calc`/
-- `simp` steps over category composition rely on defeq (not syntactic) object matching.
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits

/-- `A` *has exact countable direct sums* if countable coproducts exist in `A` and, for every
countable index set `J`, the direct sum functor `colim : (Discrete J ⥤ A) ⥤ A`,
`(Aⱼ)ⱼ ↦ ⊕ⱼ Aⱼ`, is exact.

For an additive functor between abelian categories, exactness is preservation of finite limits
and of finite colimits, and both are recorded. -/
structure HasExactCountableDirectSums (A : Type*) [Category A] [Abelian A] : Prop where
  /-- Countable coproducts exist in `A`. -/
  hasCoproducts : HasCountableCoproducts A
  /-- For every countable `J`, the direct sum functor `colim` is exact.  The
  `HasCoproductsOfShape J A` instance needed to state this is derived from `hasCoproducts`
  rather than assumed separately. -/
  exact_colim : ∀ (J : Type) [Countable J],
    haveI : HasCoproductsOfShape J A := hasCoproducts.1 J
    PreservesFiniteLimits (colim (J := Discrete J) (C := A)) ∧
    PreservesFiniteColimits (colim (J := Discrete J) (C := A))

universe t w v u

variable (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-! ### The termwise direct sum is a coproduct in the homotopy category

To give a map out of `quotient.obj (∐ K)` in `K(A)` is to give a homotopy class of complex maps
out of `∐ K`, and precomposing with `quotient.map (Sigma.ι K j)` reads off its `j`-th leg. For
existence, lift each leg along the full functor `quotient`, assemble the lifts by the universal
property of `∐ K` in `CochainComplex A ℤ`, and push the result down. For uniqueness, two lifts
agreeing up to homotopy on each `K j` are homotopic, the homotopies being assembled degreewise
(`assemble`) — which is where `[HasCoproductsOfShape J A]` is used: it makes `∐ K` a degreewise
coproduct, so a map out of `(∐ K).X n` is determined by, and can be built from, its legs. No
exactness of `A` enters. Unlike the finite case, which Mathlib gets from additivity alone, the
countable case has to be built by hand.
-/

namespace HomotopyCategoryCoproduct

/-- The degreewise colimit: `(∐K).X n` is the coproduct of `(K j).X n`. -/
noncomputable def cdeg {J : Type t} [HasCoproductsOfShape J A] (K : J → CochainComplex A ℤ)
    (n : ℤ) :
    IsColimit ((HomologicalComplex.eval A (ComplexShape.up ℤ) n).mapCocone
      (Cofan.mk (∐ K) (Sigma.ι K))) :=
  isColimitOfPreserves _ (coproductIsCoproduct K)

omit [HasDerivedCategory A] in
/-- The `j`-th leg of the degree-`n` cocone of `cdeg` is the degree-`n` component of the
coproduct injection `Sigma.ι K j`. -/
@[simp] lemma cdeg_inj {J : Type t} [HasCoproductsOfShape J A] (K : J → CochainComplex A ℤ)
    (n : ℤ) (j : J) :
    ((HomologicalComplex.eval A (ComplexShape.up ℤ) n).mapCocone
      (Cofan.mk (∐ K) (Sigma.ι K))).ι.app ⟨j⟩ = (Sigma.ι K j).f n := by
  simp [HomologicalComplex.eval, Cofan.mk]

/-- Assembled degreewise homotopy data from per-leg homotopy data. -/
noncomputable def homData {J : Type t} [HasCoproductsOfShape J A] (K : J → CochainComplex A ℤ)
    (Y : CochainComplex A ℤ) (H : ∀ j, (i k : ℤ) → (K j).X i ⟶ Y.X k) (n m : ℤ) :
    (∐ K).X n ⟶ Y.X m :=
  (cdeg A K n).desc { pt := Y.X m, ι := Discrete.natTrans (fun ⟨j⟩ => H j n m) }

omit [HasDerivedCategory A] in
/-- Restricting `homData` along the `j`-th coproduct injection recovers the `j`-th datum. -/
lemma homData_fac {J : Type t} [HasCoproductsOfShape J A] (K : J → CochainComplex A ℤ)
    (Y : CochainComplex A ℤ) (H : ∀ j, (i k : ℤ) → (K j).X i ⟶ Y.X k) (n m : ℤ) (j : J) :
    (Sigma.ι K j).f n ≫ homData A K Y H n m = H j n m := by
  have := (cdeg A K n).fac { pt := Y.X m, ι := Discrete.natTrans (fun ⟨j⟩ => H j n m) } ⟨j⟩
  simp only [HomologicalComplex.eval, Functor.mapCocone, Cofan.mk,
    Functor.const_obj_obj, Discrete.natTrans_app] at this
  rw [homData]; exact this

/-- **Homotopy assembly**: a homotopy `f ~ g : ∐K ⟶ Y` from per-leg homotopies
`Sigma.ι K j ≫ f ~ Sigma.ι K j ≫ g`. -/
noncomputable def assemble {J : Type t} [HasCoproductsOfShape J A] (K : J → CochainComplex A ℤ)
    (Y : CochainComplex A ℤ) (f g : (∐ K) ⟶ Y)
    (H : ∀ j, Homotopy (Sigma.ι K j ≫ f) (Sigma.ι K j ≫ g)) :
    Homotopy f g where
  hom n m := homData A K Y (fun j => (H j).hom) n m
  zero n m hnm := by
    apply (cdeg A K n).hom_ext
    rintro ⟨j⟩
    have e1 : ((HomologicalComplex.eval A (ComplexShape.up ℤ) n).mapCocone
        (Cofan.mk (∐ K) (Sigma.ι K))).ι.app ⟨j⟩ ≫ homData A K Y (fun j => (H j).hom) n m
        = (H j).hom n m := by rw [cdeg_inj]; exact homData_fac A K Y _ n m j
    rw [e1, show ((HomologicalComplex.eval A (ComplexShape.up ℤ) n).mapCocone
        (Cofan.mk (∐ K) (Sigma.ι K))).ι.app ⟨j⟩ ≫ (0 : (∐K).X n ⟶ Y.X m) = 0 from comp_zero]
    exact (H j).zero n m hnm
  comm n := by
    apply (cdeg A K n).hom_ext
    rintro ⟨j⟩
    have hd : (Sigma.ι K j).f n ≫ (dNext n) (fun a b => homData A K Y (fun j => (H j).hom) a b)
        = (dNext n) (H j).hom := by
      rw [dNext_eq _ (by simp : (ComplexShape.up ℤ).Rel n (n+1)),
          dNext_eq _ (by simp : (ComplexShape.up ℤ).Rel n (n+1)),
          ← Category.assoc, (Sigma.ι K j).comm n (n+1), Category.assoc, homData_fac]
    have hp : (Sigma.ι K j).f n ≫ (prevD n) (fun a b => homData A K Y (fun j => (H j).hom) a b)
        = (prevD n) (H j).hom := by
      rw [prevD_eq _ (by simp : (ComplexShape.up ℤ).Rel (n-1) n),
          prevD_eq _ (by simp : (ComplexShape.up ℤ).Rel (n-1) n),
          ← Category.assoc, homData_fac]
    have key := (H j).comm n
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f] at key
    change (Sigma.ι K j).f n ≫ _ = (Sigma.ι K j).f n ≫ _
    rw [Preadditive.comp_add, Preadditive.comp_add, hd, hp, key]

/-- The descent map into a homotopy-category cocone target, built using fullness of `quotient`. -/
noncomputable def descTo {J : Type t} (K : J → CochainComplex A ℤ) [HasCoproduct K]
    (P : HomotopyCategory A (ComplexShape.up ℤ))
    (inj : ∀ j, (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (K j) ⟶ P) :
    (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (∐ K) ⟶ P :=
  (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
    (Sigma.desc (fun j => (HomotopyCategory.quotient A (ComplexShape.up ℤ)).preimage
      (inj j : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (K j)
        ⟶ (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P.as)))

omit [HasDerivedCategory A] in
/-- `descTo` restricts along the image of the `j`-th coproduct injection to the `j`-th leg. -/
lemma descTo_fac {J : Type t} (K : J → CochainComplex A ℤ) [HasCoproduct K]
    (P : HomotopyCategory A (ComplexShape.up ℤ))
    (inj : ∀ j, (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (K j) ⟶ P) (j : J) :
    (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (Sigma.ι K j) ≫ descTo A K P inj
      = inj j := by
  rw [descTo, ← Functor.map_comp, Sigma.ι_desc, Functor.map_preimage]

/-- The clean cofan `IsColimit` for the image under `quotient`. -/
noncomputable def cleanColimit {J : Type t} [HasCoproductsOfShape J A]
    (K : J → CochainComplex A ℤ) :
    IsColimit (Cofan.mk ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (∐ K))
      (fun j => (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (Sigma.ι K j))) := by
  refine Cofan.IsColimit.mk _ (fun s => descTo A K s.pt (fun j => s.inj j))
    (fun s j => descTo_fac A K s.pt _ j) (fun s m hm => ?_)
  obtain ⟨mc, rfl⟩ : ∃ mc, (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map mc = m :=
    ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).preimage m,
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map_preimage m⟩
  refine HomotopyCategory.eq_of_homotopy _ _ (assemble A K _ _ _ (fun j => ?_))
  refine HomotopyCategory.homotopyOfEq _ _ ?_
  rw [Functor.map_comp]
  have hmj : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (Sigma.ι K j)
      ≫ (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map mc = s.inj j := hm j
  rw [hmj, ← descTo_fac A K s.pt (fun j => s.inj j) j, descTo, ← Functor.map_comp]

end HomotopyCategoryCoproduct

omit [HasDerivedCategory A] in
open HomotopyCategoryCoproduct in
/-- The homotopy quotient carries the termwise direct-sum cofan of a countable family of
complexes to a coproduct cofan in `K(A)`. -/
theorem homotopyCategory_termwiseDirectSum_isColimit
    (J : Type) [Countable J] (K : J → CochainComplex A ℤ)
    [HasCoproductsOfShape J A] [HasCoproduct K] :
    Nonempty (IsColimit ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).mapCocone
      (Cofan.mk (∐ K) (Sigma.ι K)))) :=
  ⟨(isColimitMapCoconeCofanMkEquiv (HomotopyCategory.quotient A (ComplexShape.up ℤ)) K
    (Sigma.ι K)).symm (cleanColimit A K)⟩

omit [HasDerivedCategory A] in
/-- **The homotopy category has `J`-indexed coproducts** as soon as `A` does.  Since `quotient`
is the identity on objects, every family in `K(A)` is the image of a family of complexes, and
`cleanColimit` exhibits the termwise direct sum of the latter as its coproduct. -/
theorem homotopyCategory_hasCoproductsOfShape
    (J : Type) [Countable J] [HasCoproductsOfShape J A] :
    HasCoproductsOfShape J (HomotopyCategory A (ComplexShape.up ℤ)) := by
  refine ⟨fun F => ?_⟩
  -- Reuse the cofan colimit `cleanColimit` for the family of underlying complexes.
  have hco : HasCoproduct (fun j => F.obj ⟨j⟩) :=
    ⟨⟨_, HomotopyCategoryCoproduct.cleanColimit A (fun j => (F.obj ⟨j⟩).as)⟩⟩
  -- `F` is isomorphic to the discrete functor on its object-family.
  exact hasColimit_of_iso (F := Discrete.functor (fun j => F.obj ⟨j⟩))
    (Discrete.natIso (fun ⟨j⟩ => Iso.refl _))

/-! ### Homology commutes with countable direct sums

A morphism of `K(A)` is a quasi-isomorphism when every `Hⁿ` sends it to an isomorphism, so the
stability of quasi-isomorphisms under `J`-coproducts follows once each `Hⁿ` on `K(A)` preserves
`J`-coproducts.  That is the only place exactness of countable direct sums is used, and it enters
as follows: `colim : (Discrete J ⥤ A) ⥤ A` is additive and exact, hence preserves homology, and
`ShortComplex.homologyFunctorIso` turns that into the statement that homology of a short complex
in `Discrete J ⥤ A` — which is computed pointwise — is the direct sum of the homologies.  Reading
`Hⁿ` on `CochainComplex A ℤ` as the degreewise short complex `Kⁿ⁻¹ ⟶ Kⁿ ⟶ Kⁿ⁺¹` followed by
`ShortComplex.homologyFunctor`, and using that coproducts of complexes are degreewise, gives
`Hⁿ` on `C(A)`; the statement on `K(A)` is then reflected along `quotient`, which is essentially
surjective and preserves `J`-coproducts.
-/

/-- **Reflection of `Discrete J`-colimits.** If `F : C ⥤ D` is essentially surjective and
preserves `Discrete J`-colimits, `C` has them, and the composite `F ⋙ G` preserves them, then `G`
preserves them.

Every family in `D` is, up to isomorphism, the `F`-image of a family in `C`, whose colimit cocone
`F` carries to a colimit cocone and `F ⋙ G` to a colimit cocone; so `G` preserves that one, hence
every `Discrete J`-colimit.

The restriction to the shape `Discrete J` is not cosmetic: for a general shape the lift of a
diagram along `F` has to be functorial, which needs `F` faithful, and the intended `F` here is
`HomotopyCategory.quotient`, which is not.  A family of objects has no morphisms to lift, so
essential surjectivity is all that is used. -/
theorem preservesColimitsOfShape_discrete_of_essSurj_comp
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : D ⥤ E) (J : Type*)
    [HasColimitsOfShape (Discrete J) C]
    [F.EssSurj] [PreservesColimitsOfShape (Discrete J) F]
    [PreservesColimitsOfShape (Discrete J) (F ⋙ G)] :
    PreservesColimitsOfShape (Discrete J) G := by
  refine ⟨fun {K} => ?_⟩
  let K' : Discrete J ⥤ C := Discrete.functor (fun j => F.objPreimage (K.obj ⟨j⟩))
  have α : K' ⋙ F ≅ K :=
    Discrete.natIso (fun j => F.objObjPreimageIso (K.obj j))
  have hcC : IsColimit (colimit.cocone K') := colimit.isColimit _
  have hFcC : IsColimit (F.mapCocone (colimit.cocone K')) := isColimitOfPreserves F hcC
  have : PreservesColimit (K' ⋙ F) G :=
    preservesColimit_of_preserves_colimit_cocone hFcC (isColimitOfPreserves (F ⋙ G) hcC)
  exact preservesColimit_of_iso_diagram G α

namespace L3Aux

/-- Pointwise-homology natural iso: the homology of a short complex in the functor
category `Discrete J ⥤ A` is computed objectwise.  Concretely, identifying
`ShortComplex (Discrete J ⥤ A)` with `Discrete J ⥤ ShortComplex A` via
`ShortComplex.functorEquivalence`, taking homology equals taking homology pointwise.
The objectwise iso is `ShortComplex.homologyFunctorIso (evaluation j)` (each evaluation
functor preserves homology); naturality in `j` is trivial since `Discrete J` has only
identity morphisms, and naturality in the diagram is `mapHomologyIso_inv_naturality`. -/
noncomputable def homπ (J : Type) :
    (ShortComplex.functorEquivalence (Discrete J) A).inverse ⋙ ShortComplex.homologyFunctor
        (Discrete J ⥤ A)
      ≅ (Functor.whiskeringRight (Discrete J) (ShortComplex A) A).obj (ShortComplex.homologyFunctor
          A) :=
  NatIso.ofComponents
    (fun K => NatIso.ofComponents
      (fun j => (ShortComplex.homologyFunctorIso ((evaluation (Discrete J) A).obj j)).symm.app
        ((ShortComplex.functorEquivalence (Discrete J) A).inverse.obj K))
      (by rintro ⟨i⟩ ⟨j⟩ f
          obtain rfl : i = j := Discrete.eq_of_hom f
          obtain rfl : f = 𝟙 _ := by subsingleton
          simp))
    (by intro X Y f; ext ⟨j⟩
        dsimp [ShortComplex.homologyFunctorIso]
        exact ShortComplex.mapHomologyIso_inv_naturality
          ((ShortComplex.functorEquivalence (Discrete J) A).inverse.map f)
          ((evaluation (Discrete J) A).obj ⟨j⟩))

omit [HasDerivedCategory A] in
/-- The components of the inverse of `homπ`. -/
lemma homπ_inv_app_app (J : Type) (K : Discrete J ⥤ ShortComplex A) (j : Discrete J) :
    ((homπ A J).app K).inv.app j
      = (ShortComplex.homologyFunctorIso ((evaluation (Discrete J) A).obj j)).hom.app
          ((ShortComplex.functorEquivalence (Discrete J) A).inverse.obj K) := by
  simp [homπ]

/-- The termwise coproduct cocone of a `Discrete J`-family of short complexes: the
coproduct in `ShortComplex A` computed termwise (= `colim.mapShortComplex` of the family
viewed as a short complex of `Discrete J ⥤ A`). -/
noncomputable def termCofan (J : Type) [Countable J] [HasCoproductsOfShape J A]
    (K : Discrete J ⥤ ShortComplex A) : Cocone K where
  pt := (colim (J:=Discrete J) (C:=A)).mapShortComplex.obj
      ((ShortComplex.functorEquivalence (Discrete J) A).inverse.obj K)
  ι := {
    app := fun j => ShortComplex.homMk (colimit.ι (K ⋙ ShortComplex.π₁) j)
      (colimit.ι (K ⋙ ShortComplex.π₂) j) (colimit.ι (K ⋙ ShortComplex.π₃) j)
      (ι_colimMap _ _) (ι_colimMap _ _)
    naturality := by
      rintro ⟨i⟩ ⟨j⟩ f
      obtain rfl : i = j := Discrete.eq_of_hom f
      obtain rfl : f = 𝟙 _ := by subsingleton
      ext <;> simp }

/-- The termwise coproduct cocone is a colimit: checked componentwise via
`ShortComplex.isColimitOfIsColimitπ`, each component being the colimit cocone of
`K ⋙ πᵢ`. -/
noncomputable def termIsColimit (J : Type) [Countable J] [HasCoproductsOfShape J A]
    (K : Discrete J ⥤ ShortComplex A) : IsColimit (termCofan A J K) := by
  refine ShortComplex.isColimitOfIsColimitπ _ ?_ ?_ ?_
  · exact (colimit.isColimit (K ⋙ ShortComplex.π₁)).ofIsoColimit
      (Cocone.ext (Iso.refl _) (by intro j; simp [termCofan]))
  · exact (colimit.isColimit (K ⋙ ShortComplex.π₂)).ofIsoColimit
      (Cocone.ext (Iso.refl _) (by intro j; simp [termCofan]))
  · exact (colimit.isColimit (K ⋙ ShortComplex.π₃)).ofIsoColimit
      (Cocone.ext (Iso.refl _) (by intro j; simp [termCofan]))

omit [HasDerivedCategory A] in
/-- The leg-compatibility identity: `homologyFunctorIso colim` together with pointwise
homology (`homπ`) turns the termwise coproduct legs into the colimit injections of the
homology family.  This is the homology naturality `homologyMap_mapNatTrans` applied to the
colimit-cocone natural transformation `colim.ι j : evaluation j ⟶ colim`. -/
lemma legEq (J : Type) [Countable J] [HasCoproductsOfShape J A]
    [(colim (J := Discrete J) (C := A)).PreservesHomology] (K : Discrete J ⥤ ShortComplex A) (j :
        Discrete J) :
    (ShortComplex.homologyFunctorIso ((evaluation (Discrete J) A).obj j)).hom.app
        ((ShortComplex.functorEquivalence (Discrete J) A).inverse.obj K) ≫
      colimit.ι ((ShortComplex.homologyFunctor (Discrete J ⥤ A)).obj
          ((ShortComplex.functorEquivalence (Discrete J) A).inverse.obj K)) j ≫
        ((ShortComplex.homologyFunctorIso (colim (J:=Discrete J) (C:=A))).app
            ((ShortComplex.functorEquivalence (Discrete J) A).inverse.obj K)).inv
      = (ShortComplex.homologyFunctor A).map
          (((ShortComplex.functorEquivalence (Discrete J) A).inverse.obj K).mapNatTrans
            (Limits.colim.ι (J:=Discrete J) (C:=A) j)) := by
  rw [ShortComplex.homologyFunctor_map, ShortComplex.homologyMap_mapNatTrans]
  simp only [ShortComplex.homologyFunctorIso, NatIso.ofComponents_hom_app,
    NatIso.ofComponents_inv_app, Iso.app_inv]
  rfl

/-- The point isomorphism `H(∐ⱼ Sⱼ) ≅ ∐ⱼ H(Sⱼ)`, assembled from `homologyFunctorIso colim`
(homology commutes with the exact coproduct functor) and pointwise homology (`homπ`). -/
noncomputable def pointIso (J : Type) [Countable J] [HasCoproductsOfShape J A]
    [(colim (J := Discrete J) (C := A)).PreservesHomology] (K : Discrete J ⥤ ShortComplex A) :
    (ShortComplex.homologyFunctor A).obj
        ((colim (J:=Discrete J) (C:=A)).mapShortComplex.obj
          ((ShortComplex.functorEquivalence (Discrete J) A).inverse.obj K))
      ≅ colimit (K ⋙ ShortComplex.homologyFunctor A) :=
  ((ShortComplex.homologyFunctorIso (colim (J:=Discrete J) (C:=A))).app
      ((ShortComplex.functorEquivalence (Discrete J) A).inverse.obj K)) ≪≫
    (colim (J:=Discrete J) (C:=A)).mapIso ((homπ A J).app K)

/-- `homologyFunctor` carries the termwise coproduct colimit cocone to a colimit cocone. -/
noncomputable def mappedIsColimit (J : Type) [Countable J] [HasCoproductsOfShape J A]
    [(colim (J := Discrete J) (C := A)).PreservesHomology] (K : Discrete J ⥤ ShortComplex A) :
    IsColimit ((ShortComplex.homologyFunctor A).mapCocone (termCofan A J K)) :=
  (colimit.isColimit (K ⋙ ShortComplex.homologyFunctor A)).ofIsoColimit
    (Cocone.ext (pointIso A J K).symm (by
      intro j
      have hleg : (termCofan A J K).ι.app j
          = ((ShortComplex.functorEquivalence (Discrete J) A).inverse.obj K).mapNatTrans
              (Limits.colim.ι (J:=Discrete J) (C:=A) j) := by
        ext <;> rfl
      simp only [pointIso, Iso.symm_hom, Iso.trans_inv, Functor.mapIso_inv,
        Functor.mapCocone_ι_app, colimit.cocone_ι]
      rw [colim_map, ι_colimMap_assoc, homπ_inv_app_app, hleg]
      exact legEq A J K j))

end L3Aux

omit [HasDerivedCategory A] in
/-- **`ShortComplex.homologyFunctor` commutes with `J`-coproducts** — the analytic heart of the
lemma, and the only place exactness is used.  The `Discrete J`-coproduct functor
`colim : (Discrete J ⥤ A) ⥤ A` is additive and, by `h.exact_colim J`, preserves finite
limits and finite colimits, hence has `Functor.PreservesHomology` (`inferInstance`).
`ShortComplex.homologyFunctorIso colim` then gives the natural iso
`colim.mapShortComplex ⋙ homologyFunctor ≅ homologyFunctor ⋙ colim`, which, reindexed via
`ShortComplex (Discrete J ⥤ A) ≃ Discrete J ⥤ ShortComplex A` and termwise coproducts in
`ShortComplex A`, is exactly the coproduct-comparison map for `ShortComplex.homologyFunctor`. -/
theorem shortComplex_homologyFunctor_preservesCoproducts
    (h : HasExactCountableDirectSums A) (J : Type) [Countable J]
    [HasCoproductsOfShape J A] :
    PreservesColimitsOfShape (Discrete J) (ShortComplex.homologyFunctor A) := by
  obtain ⟨hpl, hpc⟩ := h.exact_colim J
  have := hpl
  have := hpc
  have : (colim (J := Discrete J) (C := A)).PreservesHomology := inferInstance
  exact
    { preservesColimit := fun {K} =>
        preservesColimit_of_preserves_colimit_cocone (L3Aux.termIsColimit A J K)
          (L3Aux.mappedIsColimit A J K) }

omit [HasDerivedCategory A] in
/-- **`Hⁿ` on `C(A)` preserves `J`-coproducts.**  Via
`HomologicalComplex.homologyFunctorIso`, `Hⁿ` is the degreewise short complex
`Kⁿ⁻¹ ⟶ Kⁿ ⟶ Kⁿ⁺¹` followed by `ShortComplex.homologyFunctor`; the first factor preserves
`J`-coproducts because coproducts of complexes are degreewise, and the second by
`shortComplex_homologyFunctor_preservesCoproducts`. -/
theorem homologicalComplex_homologyFunctor_preservesCoproducts
    (h : HasExactCountableDirectSums A) (J : Type) [Countable J]
    [HasCoproductsOfShape J A] (n : ℤ) :
    PreservesColimitsOfShape (Discrete J)
      (HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) n) := by
  have : PreservesColimitsOfShape (Discrete J)
      (HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) n) :=
    ⟨fun {K} => preservesColimit_of_preserves_colimit_cocone (colimit.isColimit K)
      (ShortComplex.isColimitOfIsColimitπ _
        (isColimitOfPreserves (HomologicalComplex.eval A (ComplexShape.up ℤ)
          ((ComplexShape.up ℤ).prev n)) (colimit.isColimit K))
        (isColimitOfPreserves (HomologicalComplex.eval A (ComplexShape.up ℤ) n)
          (colimit.isColimit K))
        (isColimitOfPreserves (HomologicalComplex.eval A (ComplexShape.up ℤ)
          ((ComplexShape.up ℤ).next n)) (colimit.isColimit K)))⟩
  have := shortComplex_homologyFunctor_preservesCoproducts A h J
  have : PreservesColimitsOfShape (Discrete J)
      (HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) n ⋙
        ShortComplex.homologyFunctor A) := inferInstance
  exact preservesColimitsOfShape_of_natIso
    (HomologicalComplex.homologyFunctorIso A (ComplexShape.up ℤ) n).symm

omit [HasDerivedCategory A] in
/-- **The homotopy quotient preserves `J`-coproducts**: it carries the termwise direct-sum cofan,
which is a coproduct cofan of `CochainComplex A ℤ`, to a coproduct cofan of `K(A)`
(`homotopyCategory_termwiseDirectSum_isColimit`). -/
theorem homotopyCategory_quotient_preservesCoproducts
    (J : Type) [Countable J] [HasCoproductsOfShape J A] :
    PreservesColimitsOfShape (Discrete J)
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)) := by
  have (K : J → CochainComplex A ℤ) :
      PreservesColimit (Discrete.functor K) (HomotopyCategory.quotient A (ComplexShape.up ℤ)) :=
    preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct K)
      (homotopyCategory_termwiseDirectSum_isColimit A J K).some
  exact preservesColimitsOfShape_of_discrete _

omit [HasDerivedCategory A] in
/-- **`Hⁿ` on `K(A)` preserves `J`-coproducts.** The quotient `C(A) ⥤ K(A)` is essentially
surjective and preserves `J`-coproducts, and `homologyFunctorFactors` identifies its composite
with `Hⁿ` on `K(A)` with `Hⁿ` on `C(A)`, which preserves `J`-coproducts by
`homologicalComplex_homologyFunctor_preservesCoproducts`; the reflection lemma
`preservesColimitsOfShape_discrete_of_essSurj_comp` transfers this to `K(A)`. -/
theorem homotopyCategory_homologyFunctor_preservesCoproducts
    (h : HasExactCountableDirectSums A) (J : Type) [Countable J]
    [HasCoproductsOfShape J A] (n : ℤ) :
    PreservesColimitsOfShape (Discrete J)
      (HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) n) := by
  have := homotopyCategory_quotient_preservesCoproducts A J
  have := homologicalComplex_homologyFunctor_preservesCoproducts A h J n
  have : PreservesColimitsOfShape (Discrete J)
      (HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙
        HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) n) :=
    preservesColimitsOfShape_of_natIso
      (HomotopyCategory.homologyFunctorFactors A (ComplexShape.up ℤ) n).symm
  exact preservesColimitsOfShape_discrete_of_essSurj_comp
    (HomotopyCategory.quotient A (ComplexShape.up ℤ))
    (HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) n) J

omit [HasDerivedCategory A] in
/-- **Quasi-isomorphisms of `K(A)` are stable under countable direct sums**: each `Hⁿ` commutes
with `J`-coproducts, so it sends a coproduct of quasi-isomorphisms to a coproduct of
isomorphisms. -/
theorem homotopyCategory_quasiIso_stableUnderCoproducts
    (h : HasExactCountableDirectSums A) (J : Type) [Countable J] :
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).IsStableUnderCoproductsOfShape J := by
  have : HasCoproductsOfShape J A := (h.hasCoproducts).1 J
  have hpres : ∀ n, PreservesColimitsOfShape (Discrete J)
      (HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) n) :=
    fun n => homotopyCategory_homologyFunctor_preservesCoproducts A h J n
  apply MorphismProperty.IsStableUnderCoproductsOfShape.mk
  intro X₁ X₂ _ _ f hf
  rw [HomotopyCategory.mem_quasiIso_iff]
  intro n
  have := hpres n
  have : ∀ j, IsIso ((HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) n).map (f j)) :=
    fun j => (HomotopyCategory.mem_quasiIso_iff _).mp (hf j) n
  set F := HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) n
  have hcomm : sigmaComparison F X₁ ≫ F.map (Limits.Sigma.map f)
      = Limits.Sigma.map (fun j => F.map (f j)) ≫ sigmaComparison F X₂ := by
    ext j
    rw [ι_comp_sigmaComparison_assoc, ← F.map_comp, Sigma.ι_map, F.map_comp,
      Sigma.ι_map_assoc, ι_comp_sigmaComparison]
  have : IsIso (sigmaComparison F X₁) := by infer_instance
  have : IsIso (sigmaComparison F X₂) := by infer_instance
  have : IsIso (Limits.Sigma.map (fun j => F.map (f j))) := by
    refine ⟨Limits.Sigma.map (fun j => inv (F.map (f j))), ?_, ?_⟩ <;> (ext j; simp)
  have : F.map (Limits.Sigma.map f)
      = inv (sigmaComparison F X₁) ≫ Limits.Sigma.map (fun j => F.map (f j)) ≫
        sigmaComparison F X₂ := by
    rw [← hcomm]; simp
  rw [this]; infer_instance

/-- **The pointwise morphism property on a product category has a left calculus of
fractions.**

If each `W j` admits a left calculus of fractions, so does `MorphismProperty.pi W` on
the product category `∀ j, C j`, for **arbitrary** `J` (no finiteness).  A left/right
fraction of the product is assembled componentwise: `Y' := fun j => (φ j).Y'`, and
`MorphismProperty.pi W s ↔ ∀ j, W j (s j)` holds by `Iff.rfl`. -/
theorem morphismProperty_pi_hasLeftCalculusOfFractions
    {J : Type} {C : J → Type*} [∀ j, Category (C j)] (W : ∀ j, MorphismProperty (C j))
    [∀ j, (W j).HasLeftCalculusOfFractions] :
    (MorphismProperty.pi W).HasLeftCalculusOfFractions := by
  have : (MorphismProperty.pi W).IsMultiplicative :=
    { id_mem := fun X j => (W j).id_mem (X j)
      comp_mem := fun f g hf hg j => (W j).comp_mem _ _ (hf j) (hg j) }
  refine ⟨fun X Y φ => ?_, fun X' X Y f₁ f₂ s hs hfs => ?_⟩
  · choose ψ hψ using fun j => MorphismProperty.HasLeftCalculusOfFractions.exists_leftFraction
      (MorphismProperty.RightFraction.mk (φ.s j) (φ.hs j) (φ.f j))
    exact ⟨{ Y' := fun j => (ψ j).Y', f := fun j => (ψ j).f, s := fun j => (ψ j).s,
             hs := fun j => (ψ j).hs }, funext hψ⟩
  · choose Y' t ht hfeq using fun j => MorphismProperty.HasLeftCalculusOfFractions.ext
      (f₁ j) (f₂ j) (s j) (hs j) (congrFun hfs j)
    exact ⟨Y', t, ht, funext hfeq⟩

/-- **The value of a product inverse is the componentwise inverse.**  If `f : X ⟶ Y` in a product
category `∀ j, D j` is an isomorphism then so is each component `f j` (`isIso_pi_iff`), and
`(inv f) j = inv (f j)`. -/
theorem inv_pi_apply {J : Type} {D : J → Type*} [∀ j, Category (D j)]
    {X Y : ∀ j, D j} (f : X ⟶ Y) [hf : IsIso f] (j : J) :
    haveI : IsIso (f j) := (isIso_pi_iff f).mp hf j
    (inv f) j = inv (f j) := by
  have : IsIso (f j) := (isIso_pi_iff f).mp hf j
  apply IsIso.eq_inv_of_hom_inv_id
  have h := IsIso.hom_inv_id f
  exact congrFun h j

/-- **The product functor inverts the product morphism property.**  If each `s j` lies in `W j`
then each `(L j).map (s j)` is an isomorphism, and an isomorphism of a product category is
detected componentwise (`isIso_pi_iff`). -/
theorem functorPi_pi_isInvertedBy {J : Type} {C : J → Type*} {D : J → Type*}
    [∀ j, Category (C j)] [∀ j, Category (D j)]
    (L : ∀ j, C j ⥤ D j) (W : ∀ j, MorphismProperty (C j))
    [∀ j, (W j).ContainsIdentities] [∀ j, (L j).IsLocalization (W j)] :
    (MorphismProperty.pi W).IsInvertedBy (Functor.pi L) := by
  intro X Y s hs
  rw [isIso_pi_iff]
  intro j
  exact Localization.inverts (L j) (W j) _ (hs j)

/-- **The product of essentially surjective functors is essentially surjective.**  The
componentwise preimages of `Y : ∀ j, D j` assemble, along with their isomorphisms
`(L j).obj (X j) ≅ Y j`, into `(Functor.pi L).obj X ≅ Y` (`Pi.isoMk`). -/
theorem functorPi_essSurj {J : Type} {C : J → Type*} {D : J → Type*}
    [∀ j, Category (C j)] [∀ j, Category (D j)]
    (L : ∀ j, C j ⥤ D j) [∀ j, (L j).EssSurj] :
    (Functor.pi L).EssSurj := by
  constructor; intro Y
  exact ⟨fun j => (L j).objPreimage (Y j), ⟨Pi.isoMk (fun j => (L j).objObjPreimageIso (Y j))⟩⟩

/-! #### Product left fractions

The canonical functor `G' : (pi W).Localization ⥤ (∀ j, D j)` induced by `Functor.pi L` is an
equivalence, and this is where the arbitrary index type is paid for.  It is essentially
surjective because `Functor.pi L` is and `(pi W).Q` is surjective on objects.  It is fully
faithful by the left-fraction description of the Hom-sets: every morphism between objects in the
image of `Functor.pi L` is the image of a *product* left fraction, assembled componentwise from
`Localization.exists_leftFraction`, and two product fractions have the same image exactly when
they are related by a componentwise `LeftFractionRel`.  Nothing here asks an infinite product to
commute with a filtered colimit, which is what confines Mathlib's `Functor.IsLocalization.pi` to
finite index types.
-/

/-- Bridge: applying a further functor `G` to the image of a left fraction under `L`
agrees with the image under `L ⋙ G`. -/
theorem leftFraction_map_comp_functor {C D E : Type*} [Category C] [Category D] [Category E]
    (L : C ⥤ D) (G : D ⥤ E) {W : MorphismProperty C}
    {X Y : C} (φ : W.LeftFraction X Y) (hL : W.IsInvertedBy L)
    (hLG : W.IsInvertedBy (L ⋙ G)) :
    G.map (φ.map L hL) = φ.map (L ⋙ G) hLG := by
  have hs := hL φ.s φ.hs
  have hsg := hLG φ.s φ.hs
  change G.map (L.map φ.f ≫ inv (L.map φ.s)) = (L ⋙ G).map φ.f ≫ inv ((L ⋙ G).map φ.s)
  rw [G.map_comp]
  congr 1
  exact G.map_inv _

/-- The image of a `pi W`-left fraction under `Functor.pi L` is computed componentwise. -/
theorem functorPi_leftFraction_map_apply {J : Type} {C : J → Type*} {D : J → Type*}
    [∀ j, Category (C j)] [∀ j, Category (D j)]
    (L : ∀ j, C j ⥤ D j) (W : ∀ j, MorphismProperty (C j))
    [∀ j, (W j).ContainsIdentities] [∀ j, (L j).IsLocalization (W j)]
    (hinv : (MorphismProperty.pi W).IsInvertedBy (Functor.pi L))
    {X Y : ∀ j, C j} (φ : (MorphismProperty.pi W).LeftFraction X Y) (j : J) :
    (φ.map (Functor.pi L) hinv) j
      = (MorphismProperty.LeftFraction.mk (φ.f j) (φ.s j) (φ.hs j)).map (L j)
          (Localization.inverts (L j) (W j)) := by
  have : IsIso ((Functor.pi L).map φ.s) := hinv φ.s φ.hs
  change ((Functor.pi L).map φ.f ≫ inv ((Functor.pi L).map φ.s)) j = _
  have : IsIso ((L j).map (φ.s j)) := Localization.inverts (L j) (W j) _ (φ.hs j)
  change ((Functor.pi L).map φ.f) j ≫ (inv ((Functor.pi L).map φ.s)) j
      = (L j).map (φ.f j) ≫ inv ((L j).map (φ.s j))
  rw [Functor.pi_map]
  congr 1
  rw [inv_pi_apply ((Functor.pi L).map φ.s) j]
  rfl

/-- Transport the image of a left fraction along a natural isomorphism of inverting functors. -/
theorem leftFraction_map_iso_transport {C D : Type*} [Category C] [Category D]
    {W : MorphismProperty C} (F₁ F₂ : C ⥤ D) (e : F₁ ≅ F₂) {X Y : C} (φ : W.LeftFraction X Y)
    (h₁ : W.IsInvertedBy F₁) (h₂ : W.IsInvertedBy F₂) :
    φ.map F₂ h₂ = e.inv.app X ≫ φ.map F₁ h₁ ≫ e.hom.app Y := by
  have := h₁ φ.s φ.hs
  have := h₂ φ.s φ.hs
  change F₂.map φ.f ≫ inv (F₂.map φ.s) = e.inv.app X ≫ (F₁.map φ.f ≫ inv (F₁.map φ.s)) ≫ e.hom.app Y
  rw [← cancel_mono (F₂.map φ.s)]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← e.hom.naturality φ.s, ← Category.assoc (inv (F₁.map φ.s)), IsIso.inv_hom_id,
    Category.id_comp, e.hom.naturality φ.f]
  simp

/-- Two product left fractions have equal `Functor.pi L`-image iff they are related by the
product left-fraction relation (assembled componentwise). -/
theorem functorPi_leftFraction_map_eq_iff {J : Type} {C : J → Type*} {D : J → Type*}
    [∀ j, Category (C j)] [∀ j, Category (D j)]
    (L : ∀ j, C j ⥤ D j) (W : ∀ j, MorphismProperty (C j))
    [∀ j, (W j).HasLeftCalculusOfFractions]
    [∀ j, (L j).IsLocalization (W j)]
    (hinv : (MorphismProperty.pi W).IsInvertedBy (Functor.pi L))
    {X Y : ∀ j, C j} (φ ψ : (MorphismProperty.pi W).LeftFraction X Y) :
    φ.map (Functor.pi L) hinv = ψ.map (Functor.pi L) hinv ↔
      MorphismProperty.LeftFractionRel φ ψ := by
  refine ⟨fun hmap => ?_, fun ⟨Z, t₁, t₂, hs, hf, hW⟩ => funext fun j => ?_⟩
  · have hcomp (j : J) : MorphismProperty.LeftFractionRel
        (MorphismProperty.LeftFraction.mk (φ.f j) (φ.s j) (φ.hs j))
        (MorphismProperty.LeftFraction.mk (ψ.f j) (ψ.s j) (ψ.hs j)) := by
      rw [← MorphismProperty.LeftFraction.map_eq_iff (L j) (W j),
        ← functorPi_leftFraction_map_apply L W hinv φ j,
        ← functorPi_leftFraction_map_apply L W hinv ψ j]
      exact congrFun hmap j
    choose Z t₁ t₂ hs hf hW using hcomp
    exact ⟨Z, t₁, t₂, funext hs, funext hf, hW⟩
  · rw [functorPi_leftFraction_map_apply L W hinv φ j,
      functorPi_leftFraction_map_apply L W hinv ψ j]
    exact (MorphismProperty.LeftFraction.map_eq_iff (L j) (W j) _ _).mpr
      ⟨Z j, t₁ j, t₂ j, congrFun hs j, congrFun hf j, hW j⟩

/-- Every morphism `(Functor.pi L).obj X ⟶ (Functor.pi L).obj Y` is the image of a product
left fraction (assembled componentwise from `Localization.exists_leftFraction`). -/
theorem functorPi_exists_leftFraction {J : Type} {C : J → Type*} {D : J → Type*}
    [∀ j, Category (C j)] [∀ j, Category (D j)]
    (L : ∀ j, C j ⥤ D j) (W : ∀ j, MorphismProperty (C j))
    [∀ j, (W j).HasLeftCalculusOfFractions]
    [∀ j, (L j).IsLocalization (W j)]
    (hinv : (MorphismProperty.pi W).IsInvertedBy (Functor.pi L))
    {X Y : ∀ j, C j} (g : (Functor.pi L).obj X ⟶ (Functor.pi L).obj Y) :
    ∃ φ : (MorphismProperty.pi W).LeftFraction X Y, g = φ.map (Functor.pi L) hinv := by
  have hcomp : ∀ j, ∃ φj : (W j).LeftFraction (X j) (Y j),
      g j = φj.map (L j) (Localization.inverts (L j) (W j)) := by
    intro j; exact Localization.exists_leftFraction (L j) (W j) (g j)
  choose φ hφ using hcomp
  refine ⟨{ Y' := fun j => (φ j).Y', f := fun j => (φ j).f, s := fun j => (φ j).s,
            hs := fun j => (φ j).hs }, ?_⟩
  funext j
  rw [functorPi_leftFraction_map_apply L W hinv _ j]
  exact hφ j

/-- The functor `(pi W).Localization ⥤ (∀ j, D j)` induced by `Functor.pi L` is an equivalence,
for an arbitrary index type: it is essentially surjective because `Functor.pi L` is, and fully
faithful by the product left-fraction description of its Hom-sets. -/
theorem functorPi_lift_isEquivalence {J : Type} {C : J → Type*} {D : J → Type*}
    [∀ j, Category (C j)] [∀ j, Category (D j)]
    (L : ∀ j, C j ⥤ D j) (W : ∀ j, MorphismProperty (C j))
    [∀ j, (W j).HasLeftCalculusOfFractions]
    [∀ j, (L j).IsLocalization (W j)]
    [(MorphismProperty.pi W).HasLeftCalculusOfFractions] :
    (Localization.lift (Functor.pi L) (functorPi_pi_isInvertedBy L W)
      (MorphismProperty.pi W).Q).IsEquivalence := by
  set Lpi := Functor.pi L with hLpi
  set hinv := functorPi_pi_isInvertedBy L W with hhinv
  set Q := (MorphismProperty.pi W).Q with hQ
  set G' := Localization.lift Lpi hinv Q with hG'
  have fac : Q ⋙ G' ≅ Lpi := Localization.fac Lpi hinv Q
  -- each `L j` is essentially surjective (being a localization)
  have : ∀ j, (L j).EssSurj := fun j => Localization.essSurj (L j) (W j)
  have : Lpi.EssSurj := functorPi_essSurj L
  -- Essential surjectivity of `G'`: transport along `fac` through `Q` (ess-surj).
  have hQs : Q.EssSurj := Localization.essSurj Q (MorphismProperty.pi W)
  have hQG'es : (Q ⋙ G').EssSurj := Functor.essSurj_of_iso fac.symm
  have essSurj : G'.EssSurj :=
    ⟨fun Z => ⟨Q.obj ((Q ⋙ G').objPreimage Z), ⟨(Q ⋙ G').objObjPreimageIso Z⟩⟩⟩
  -- `Q` and `Q ⋙ G'` invert `pi W`.
  have invQ : (MorphismProperty.pi W).IsInvertedBy Q := Localization.inverts Q (MorphismProperty.pi
      W)
  have invQG' : (MorphismProperty.pi W).IsInvertedBy (Q ⋙ G') := by
    intro X Y s hs
    have := invQ s hs
    change IsIso (G'.map (Q.map s))
    infer_instance
  -- Bridge: `G'.map (φ.map Q invQ) = fac.hom.app X ≫ φ.map Lpi hinv ≫ fac.inv.app Y`.
  have keymap : ∀ {X Y : ∀ j, C j} (φ : (MorphismProperty.pi W).LeftFraction X Y),
      G'.map (φ.map Q invQ)
        = fac.hom.app X ≫ φ.map Lpi hinv ≫ fac.inv.app Y := by
    intro X Y φ
    rw [leftFraction_map_comp_functor Q G' φ invQ invQG']
    exact leftFraction_map_iso_transport Lpi (Q ⋙ G') fac.symm φ hinv invQG'
  -- Faithfulness of `G'`: reduce a morphism `f₁ f₂` to fractions and compare via the
  -- product `LeftFractionRel` characterisation.
  have : G'.Faithful := by
    refine ⟨fun {a b} f₁ f₂ hf => ?_⟩
    set X := Q.objPreimage a with hX
    set Y := Q.objPreimage b with hY
    set eX : Q.obj X ≅ a := Q.objObjPreimageIso a with heX
    set eY : Q.obj Y ≅ b := Q.objObjPreimageIso b with heY
    set g₁ : Q.obj X ⟶ Q.obj Y := eX.hom ≫ f₁ ≫ eY.inv with hg1
    set g₂ : Q.obj X ⟶ Q.obj Y := eX.hom ≫ f₂ ≫ eY.inv with hg2
    suffices hg : g₁ = g₂ by
      have h2 : f₁ ≫ eY.inv = f₂ ≫ eY.inv := (cancel_epi eX.hom).mp hg
      exact (cancel_mono eY.inv).mp h2
    obtain ⟨φ₁, e₁⟩ := Localization.exists_leftFraction Q (MorphismProperty.pi W) g₁
    obtain ⟨φ₂, e₂⟩ := Localization.exists_leftFraction Q (MorphismProperty.pi W) g₂
    rw [e₁, e₂]
    have hG'g : G'.map (φ₁.map Q invQ) = G'.map (φ₂.map Q invQ) := by
      rw [← e₁, ← e₂, hg1, hg2, Functor.map_comp, Functor.map_comp, Functor.map_comp,
        Functor.map_comp, hf]
    rw [keymap φ₁, keymap φ₂] at hG'g
    have hLpi : φ₁.map Lpi hinv = φ₂.map Lpi hinv := by
      rw [← cancel_epi (fac.hom.app X), ← cancel_mono (fac.inv.app Y)]
      simpa [Category.assoc] using hG'g
    rw [MorphismProperty.LeftFraction.map_eq_iff Q (MorphismProperty.pi W)]
    exact (functorPi_leftFraction_map_eq_iff L W hinv φ₁ φ₂).mp hLpi
  -- Fullness of `G'`: build a preimage fraction via `functorPi_exists_leftFraction`.
  have : G'.Full := by
    refine ⟨fun {a b} g => ?_⟩
    set X := Q.objPreimage a with hX
    set Y := Q.objPreimage b with hY
    set eX : Q.obj X ≅ a := Q.objObjPreimageIso a with heX
    set eY : Q.obj Y ≅ b := Q.objObjPreimageIso b with heY
    obtain ⟨φ, hφ⟩ := functorPi_exists_leftFraction L W hinv
      (fac.inv.app X ≫ (G'.map eX.hom ≫ g ≫ G'.map eY.inv) ≫ fac.hom.app Y)
    refine ⟨eX.inv ≫ φ.map Q invQ ≫ eY.hom, ?_⟩
    rw [Functor.map_comp, Functor.map_comp, keymap φ, ← hφ]
    have key : G'.map eX.inv ≫ fac.hom.app X ≫ fac.inv.app X ≫ G'.map eX.hom ≫ g ≫
        G'.map eY.inv ≫ fac.hom.app Y ≫ fac.inv.app Y ≫ G'.map eY.hom = g := by
      slice_lhs 2 3 => rw [fac.hom_inv_id_app]
      slice_lhs 6 7 => rw [fac.hom_inv_id_app]
      simp
    simp only [Category.assoc] at key ⊢
    exact key
  -- fully faithful + essentially surjective ⟹ equivalence.
  exact { }

/-- **A product of localizations is a localization, for any `J`.**

If each `L j : C j ⥤ D j` is a localization at `W j` and each `W j` admits a left calculus of
fractions, then `Functor.pi L : (∀ j, C j) ⥤ (∀ j, D j)` is a localization at
`MorphismProperty.pi W`, for an arbitrary index type `J`.

This generalizes `Functor.IsLocalization.pi` (`Mathlib/CategoryTheory/Localization/Pi.lean`),
which assumes `[Finite J]`. It is assembled from `functorPi_pi_isInvertedBy` and
`functorPi_lift_isEquivalence` via `Functor.IsLocalization.of_equivalence_target`. -/
theorem functor_pi_isLocalization_of_hasLeftCalculusOfFractions
    {J : Type} {C : J → Type*} {D : J → Type*}
    [∀ j, Category (C j)] [∀ j, Category (D j)]
    (L : ∀ j, C j ⥤ D j) (W : ∀ j, MorphismProperty (C j))
    [∀ j, (W j).HasLeftCalculusOfFractions]
    [∀ j, (L j).IsLocalization (W j)] :
    (Functor.pi L).IsLocalization (MorphismProperty.pi W) := by
  have := morphismProperty_pi_hasLeftCalculusOfFractions W
  have hinv := functorPi_pi_isInvertedBy L W
  have := functorPi_lift_isEquivalence L W
  -- Transport the localization `(pi W).Q` along the equivalence it induces.
  exact Functor.IsLocalization.of_equivalence_target (MorphismProperty.pi W).Q
    (MorphismProperty.pi W) (Functor.pi L)
    (Localization.lift (Functor.pi L) hinv (MorphismProperty.pi W).Q).asEquivalence
    (Localization.fac (Functor.pi L) hinv (MorphismProperty.pi W).Q)

/-- **A countable product of localizations is a localization.**

For a localization functor `L : C ⥤ D` at a morphism property `W` admitting a left
calculus of fractions (and containing identities), the whiskered functor
`(whiskeringRight (Discrete J) C D).obj L : (Discrete J ⥤ C) ⥤ (Discrete J ⥤ D)` is a
localization at the pointwise property `W.functorCategory (Discrete J)`, for **any
countable** index `J`.

Mathlib provides this for `Finite J` via
`Functor.IsLocalization.of_equivalences` applied to `Functor.pi (fun _ => L)` along the
equivalences `piEquivalenceFunctorDiscrete J C/D`, the only finiteness use being in
`Functor.IsLocalization.pi`.  Replacing that step with
`functor_pi_isLocalization_of_hasLeftCalculusOfFractions`, which needs no finiteness, gives the
countable case: the `CatCommSq`, the `≤ isoClosure.inverseImage`, and the `IsInvertedBy`
conditions are all finiteness-free (`MorphismProperty.le_isoClosure`,
`NatIso.isIso_of_isIso_app`, `MorphismProperty.IsInvertedBy.pi`).  The hypothesis
`Countable J` is in fact not used.

The finite analogue is the `Discrete J` localization instance in
`Mathlib/CategoryTheory/Localization/Pi.lean`. -/
theorem localizationFunctorCategory_discrete_isLocalization_of_countable
    {C : Type*} {D : Type*} [Category C] [Category D] (L : C ⥤ D) (W : MorphismProperty C)
    [L.IsLocalization W] [W.HasLeftCalculusOfFractions]
    (J : Type) [Countable J] :
    ((Functor.whiskeringRight (Discrete J) C D).obj L).IsLocalization
      (W.functorCategory (Discrete J)) := by
  -- `Functor.pi (fun _ => L)` is a localization at `MorphismProperty.pi`.
  have : (Functor.pi (fun _ : J => L)).IsLocalization (MorphismProperty.pi (fun _ : J => W)) :=
    functor_pi_isLocalization_of_hasLeftCalculusOfFractions (fun _ => L) (fun _ => W)
  let E := piEquivalenceFunctorDiscrete J C
  let E' := piEquivalenceFunctorDiscrete J D
  -- Assemble via `Functor.IsLocalization.of_equivalences` along `E`, `E'`:
  --   * `CatCommSq E.functor (Functor.pi (fun _ => L)) ((whiskeringRight …).obj L) E'.functor`
  --     (finiteness-free; same as Mathlib's finite `Discrete J` instance),
  --   * `MorphismProperty.pi (fun _ => W) ≤
  --       (W.functorCategory (Discrete J)).isoClosure.inverseImage E.functor`
  --     via `MorphismProperty.le_isoClosure` (componentwise),
  --   * `(W.functorCategory (Discrete J)).IsInvertedBy ((whiskeringRight …).obj L)`
  --     via `NatIso.isIso_of_isIso_app` + `MorphismProperty.IsInvertedBy.pi`.
  let L₂ := (Functor.whiskeringRight (Discrete J) C D).obj L
  let L₁ := Functor.pi (fun (_ : J) => L)
  have : CatCommSq E.functor L₁ L₂ E'.functor :=
    ⟨(Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ E'.counitIso.symm ≪≫
      Functor.associator _ _ _≪≫ Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (by exact Iso.refl _) _) ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight E.unitIso.symm L₁) _ ≪≫ Functor.isoWhiskerRight L₁.leftUnitor _⟩
  refine Functor.IsLocalization.of_equivalences L₁
    (MorphismProperty.pi (fun _ => W)) L₂ _ E E' ?_ ?_
  · intro X Y f hf
    exact MorphismProperty.le_isoClosure _ _ (fun ⟨j⟩ => hf j)
  · intro X Y f hf
    have : ∀ (j : Discrete J), IsIso ((L₂.map f).app j) :=
      fun j => Localization.inverts L W _ (hf j)
    apply NatIso.isIso_of_isIso_app

/- Colimit-dual machinery for `localization_preservesCoproductsOfShape`: the
`Cocone`/`IsColimit` analogues of Mathlib's `coneOfAdj`/`isLimitConeOfAdj`, and the
colimit dual of `Localization.HasProductsOfShapeAux`. -/
namespace ColimAux

/-- Dual of `Limits.coneOfAdj`: a left adjoint to the constant functor gives a cocone. -/
def coconeOfAdj {J : Type*} [Category J] {C : Type*} [Category C] {L : (J ⥤ C) ⥤ C}
    (adj : L ⊣ Functor.const J) (F : J ⥤ C) : Cocone F where
  pt := L.obj F
  ι := adj.unit.app F

/-- Dual of `Limits.isLimitConeOfAdj`. -/
@[sga "4 V 2.3.6" "more general"]
def isColimitCoconeOfAdj {J : Type*} [Category J] {C : Type*} [Category C] {L : (J ⥤ C) ⥤ C}
    (adj : L ⊣ Functor.const J) (F : J ⥤ C) : IsColimit (coconeOfAdj adj F) where
  desc := fun s => (adj.homEquiv F s.pt).symm s.ι
  fac := fun s j => by
    have key : adj.homEquiv F s.pt ((adj.homEquiv F s.pt).symm s.ι) = s.ι :=
      (adj.homEquiv F s.pt).apply_symm_apply s.ι
    rw [adj.homEquiv_unit] at key
    have := congrArg (fun (η : F ⟶ (Functor.const J).obj s.pt) => η.app j) key
    simpa [coconeOfAdj] using this
  uniq := fun s m hm => by
    apply (adj.homEquiv F s.pt).injective
    rw [Equiv.apply_symm_apply, adj.homEquiv_unit]
    ext j
    have := hm j
    simpa [coconeOfAdj] using this

variable {C : Type*} {D : Type*} [Category C] [Category D] (L : C ⥤ D) (W : MorphismProperty C)
    [L.IsLocalization W] (J : Type) [HasCoproductsOfShape J C] [W.IsStableUnderCoproductsOfShape J]

/-- `colim ⋙ L` inverts the functor-category morphism property (colimit dual of
`HasProductsOfShapeAux.inverts`). -/
theorem inverts : (W.functorCategory (Discrete J)).IsInvertedBy (colim ⋙ L) := fun _ _ f hf =>
  Localization.inverts L W (colim.map f) (MorphismProperty.colimMap f hf)

variable [W.ContainsIdentities]
    [((Functor.whiskeringRight (Discrete J) C D).obj L).IsLocalization (W.functorCategory (Discrete
        J))]

/-- The colimit functor descended through the functor-category localization (colimit dual
of `HasProductsOfShapeAux.limitFunctor`). -/
@[reducible]
noncomputable def colimitFunctor : (Discrete J ⥤ D) ⥤ D :=
  Localization.lift (colim ⋙ L) (inverts L W J) ((Functor.whiskeringRight (Discrete J) C D).obj L)

/-- The descended-functor compatibility iso (colimit dual of `compLimitFunctorIso`). -/
noncomputable def compColimitFunctorIso :
    (Functor.whiskeringRight (Discrete J) C D).obj L ⋙ colimitFunctor L W J ≅ colim ⋙ L :=
  Localization.fac (colim ⋙ L) (inverts L W J) ((Functor.whiskeringRight (Discrete J) C D).obj L)

/-- The square formed by `colim`, the localization of `Discrete J`-diagrams, `L` and
`colimitFunctor` commutes. -/
noncomputable instance catCommSq :
    CatCommSq colim ((Functor.whiskeringRight (Discrete J) C D).obj L) L (colimitFunctor L W J) :=
  CatCommSq.mk (compColimitFunctorIso L W J).symm

/-- The descended adjunction `colimitFunctor ⊣ const` (colimit dual of
`HasProductsOfShapeAux.adj`). -/
noncomputable def adj : colimitFunctor L W J ⊣ Functor.const (Discrete J) :=
  colimConstAdj.localization ((Functor.whiskeringRight (Discrete J) C D).obj L)
    (W.functorCategory (Discrete J)) L W (colimitFunctor L W J) (Functor.const (Discrete J))

/-- `L` sends the colimit cocone of `F` to a colimit cocone (colimit dual of
`HasProductsOfShapeAux.isLimitMapCone`). -/
noncomputable def isColimitMapCocone (F : Discrete J ⥤ C) :
    IsColimit (L.mapCocone (colimit.cocone F)) :=
  (isColimitCoconeOfAdj (adj L W J) (F ⋙ L)).ofIsoColimit
    (Cocone.ext ((compColimitFunctorIso L W J).app F) (fun j => by
      have hunit := Adjunction.localization_unit_app colimConstAdj
        ((Functor.whiskeringRight (Discrete J) C D).obj L) (W.functorCategory (Discrete J)) L W
        (colimitFunctor L W J) (Functor.const (Discrete J)) F
      dsimp [coconeOfAdj, adj]
      erw [hunit]
      simp only [Functor.comp_obj, Functor.const_obj_obj, NatTrans.comp_app, Functor.const_map_app,
        CatCommSq.iso, Iso.symm_hom, Functor.whiskeringRight_obj_obj]
      dsimp [colimConstAdj, Functor.compConstIso]
      simp only [Category.assoc]
      rw [Iso.inv_hom_id_app]
      simp))

end ColimAux

/-- **A localization preserves `J`-coproducts** (the colimit dual of
`Localization.preservesProductsOfShape`).

If `L : C ⥤ D` is a localization at `W`, the category `C` has `J`-coproducts, `W` is
stable under `J`-coproducts, and the whiskered functor on `Discrete J`-diagrams is a
localization, then `L` preserves `J`-indexed coproducts.

`colim ⋙ L` inverts the pointwise `W` (`MorphismProperty.colimMap`), so it descends through the
localization on `Discrete J`-diagrams to a functor `colimitFunctor : (Discrete J ⥤ D) ⥤ D`
together with a `CatCommSq`; the descended adjunction `colimitFunctor ⊣ const` then exhibits
`L.mapCocone (colimit.cocone F)` as a colimit.  This is the argument of
`Localization.preservesProductsOfShape` in
`Mathlib/CategoryTheory/Localization/FiniteProducts.lean`, read in the dual. -/
theorem localization_preservesCoproductsOfShape
    {C : Type*} {D : Type*} [Category C] [Category D] (L : C ⥤ D) (W : MorphismProperty C)
    [L.IsLocalization W] [W.ContainsIdentities] (J : Type) [Countable J]
    [HasCoproductsOfShape J C] [W.IsStableUnderCoproductsOfShape J]
    [((Functor.whiskeringRight (Discrete J) C D).obj L).IsLocalization
      (W.functorCategory (Discrete J))] :
    PreservesColimitsOfShape (Discrete J) L := by
  exact
    { preservesColimit := fun {F} =>
        preservesColimit_of_preserves_colimit_cocone (colimit.isColimit F)
          (ColimAux.isColimitMapCocone L W J F) }

/-- **The localization `Qh : K(A) ⥤ D(A)` preserves `J`-coproducts** for countable `J`.

`D(A)` is the localization of `K(A)` at the quasi-isomorphisms `W`, which are stable under
`J`-coproducts by `homotopyCategory_quasiIso_stableUnderCoproducts` — the step that uses
exactness of countable direct sums — so `localization_preservesCoproductsOfShape` applies, its
hypothesis that `Discrete J`-diagrams localize being
`localizationFunctorCategory_discrete_isLocalization_of_countable`. -/
theorem derivedCategory_Qh_preservesCoproductsOfShape
    (h : HasExactCountableDirectSums A) (J : Type) [Countable J]
    [HasCoproductsOfShape J (HomotopyCategory A (ComplexShape.up ℤ))] :
    PreservesColimitsOfShape (Discrete J) (DerivedCategory.Qh (C := A)) := by
  have : (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).IsStableUnderCoproductsOfShape J :=
    homotopyCategory_quasiIso_stableUnderCoproducts A h J
  have := localizationFunctorCategory_discrete_isLocalization_of_countable
    (DerivedCategory.Qh (C := A)) (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) J
  exact localization_preservesCoproductsOfShape
    (DerivedCategory.Qh (C := A)) (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) J

/-! ### Statement of the lemma -/

/-- **Stacks Tag 0A5L**, in the form its proof establishes and its consumers use: if `A` has
exact countable direct sums then `Q : C(A) ⥤ D(A)` preserves countable coproducts.

`Q` is `quotient ⋙ Qh` (`DerivedCategory.quotientCompQhIso`), and both factors preserve
`J`-coproducts. -/
theorem derivedCategory_Q_preservesCoproductsOfShape
    (h : HasExactCountableDirectSums A) (J : Type) [Countable J] :
    PreservesColimitsOfShape (Discrete J) (DerivedCategory.Q (C := A)) := by
  have : HasCoproductsOfShape J A := h.hasCoproducts.1 J
  have : HasCoproductsOfShape J (HomotopyCategory A (ComplexShape.up ℤ)) :=
    homotopyCategory_hasCoproductsOfShape A J
  have := homotopyCategory_quotient_preservesCoproducts A J
  have := derivedCategory_Qh_preservesCoproductsOfShape A h J
  exact preservesColimitsOfShape_of_natIso (DerivedCategory.quotientCompQhIso A)

/-- **Stacks Tag 0A5L**, the concrete identification of the coproduct in `D(A)`: for a countable
family `K : J → CochainComplex A ℤ`, the termwise direct sum `∐ K`, with the images under `Q` of
the canonical injections `Sigma.ι K j`, is a coproduct of `(Q (K j))ⱼ` in `D(A)`.

`[HasCoproduct K]` records that the termwise direct sum exists in `CochainComplex A ℤ`; it
follows from `h.hasCoproducts` and `Countable J`, but is assumed so that `∐ K` and `Sigma.ι K`
are well-formed in the statement. -/
@[stacks 0A5L]
theorem derivedCategory_termwiseDirectSum_isColimit
    (h : HasExactCountableDirectSums A) (J : Type) [Countable J]
    (K : J → CochainComplex A ℤ) [HasCoproduct K] :
    Nonempty (IsColimit
      ((DerivedCategory.Q (C := A)).mapCocone (Cofan.mk (∐ K) (Sigma.ι K)))) :=
  have := derivedCategory_Q_preservesCoproductsOfShape A h J
  ⟨isColimitOfPreserves _ (coproductIsCoproduct K)⟩

/-- **Stacks Tag 0A5L**: if the abelian category `A` has exact countable direct sums then its
derived category `D(A)` has countable direct sums.

A countable family in `D(A)` is, up to isomorphism, the image under `Q` of a family of complexes,
by essential surjectivity of `Q`; the termwise direct sum of the latter is its coproduct. -/
@[stacks 0A5L]
theorem derivedCategory_hasCountableCoproducts
    (h : HasExactCountableDirectSums A) :
    HasCountableCoproducts (DerivedCategory A) := by
  have : HasCountableCoproducts A := h.hasCoproducts
  refine ⟨fun J _ => ⟨fun F => ?_⟩⟩
  set Q := DerivedCategory.Q (C := A)
  set K : J → CochainComplex A ℤ := fun j => Q.objPreimage (F.obj ⟨j⟩)
  obtain ⟨hc⟩ := derivedCategory_termwiseDirectSum_isColimit A h J K
  have e : Discrete.functor K ⋙ Q ≅ F :=
    Discrete.natIso (fun i => Q.objObjPreimageIso (F.obj i))
  have : HasColimit (Discrete.functor K ⋙ Q) := ⟨_, hc⟩
  exact hasColimit_of_iso e.symm

/-! ### Coproducts of an arbitrary shape, through K-injective resolutions

The lemma above uses exactness of countable direct *sums* and yields coproducts indexed by a
countable set. When `A` has enough injectives and exact countable *products* a second route is
available, with no restriction at all on the index type. A morphism out of `quotient.obj (∐ K)`
into an object of `D(A)` may be computed in `K(A)`: every object of `D(A)` is the image under `Qh`
of a K-injective complex, and `Qh` is bijective on the morphism sets into a K-injective object
(`CochainComplex.IsKInjective.Qh_map_bijective`), which is enough for `Qh` to carry a colimit
cofan to a colimit cofan. Applied to `HomotopyCategoryCoproduct.cleanColimit` this says that
`Q : C(A) ⥤ D(A)` preserves `J`-indexed coproducts for *every* shape `J` available in `A`, the
exactness hypothesis now bearing on the countable products used to build K-injective resolutions
rather than on the direct sums.
-/

section ArbitraryShape

universe v₂ u₂ v₃ u₃

/-- A functor carries a colimit cofan to a colimit cofan as soon as every object of the target is
isomorphic to the image of an object on which the functor is bijective on incoming morphism
sets.

This is pure category theory, and is stated here because this is the first place the derived
category needs it; the K-injective resolutions which supply its hypothesis for `Qh` are
`exists_map_bijective_Qh_of_exists_quasiIso_isKInjective` below. -/
theorem isColimit_mapCofan_of_exists_map_bijective
    {C : Type u₂} [Category.{v₂} C] {E : Type u₃} [Category.{v₃} E] (F : C ⥤ E)
    (hF : ∀ Y : E, ∃ I : C, ∃ _e : F.obj I ≅ Y,
      ∀ X : C, Function.Bijective (F.map : (X ⟶ I) → _))
    {J : Type*} {K : J → C} {S : C} (ι : ∀ j, K j ⟶ S) (hc : IsColimit (Cofan.mk S ι)) :
    Nonempty (IsColimit (Cofan.mk (F.obj S) fun j => F.map (ι j))) := by
  classical
  have hd : ∀ s : Cofan (fun j => F.obj (K j)),
      ∃! m : F.obj S ⟶ s.pt, ∀ j, F.map (ι j) ≫ m = s.inj j := by
    intro s
    obtain ⟨I, e, hI⟩ := hF s.pt
    choose l hl using fun j => (hI (K j)).surjective (s.inj j ≫ e.inv)
    let a := hc.desc (Cofan.mk I l)
    have ha (j : J) : ι j ≫ a = l j := hc.fac (Cofan.mk I l) ⟨j⟩
    refine ⟨F.map a ≫ e.hom, ?_, ?_⟩
    · intro j
      rw [← F.map_comp_assoc, ha, hl]
      simp
    · intro m hm
      obtain ⟨b, hb⟩ := (hI S).surjective (m ≫ e.inv)
      have hba : b = a := by
        apply hc.hom_ext
        rintro ⟨j⟩
        change ι j ≫ b = ι j ≫ a
        rw [ha]
        apply (hI (K j)).injective
        rw [F.map_comp, hb, ← Category.assoc, hm, hl]
      apply (cancel_mono e.inv).1
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rw [← hb, hba]
  exact ⟨Cofan.IsColimit.mk _ (fun s => (hd s).choose)
    (fun s => (hd s).choose_spec.1) (fun s m hm => (hd s).choose_spec.2 m hm)⟩

/-- Every object of `D(A)` is the image under `Qh` of a K-injective complex, and `Qh` is bijective
on the morphism sets into it, as soon as every cochain complex admits a quasi-isomorphism into a
K-injective one.

Where that input comes from is left to the caller, because the two available sources are
independent: exact countable products (Tag 090Y, `CochainComplex.exists_quasiIso_isKInjective`,
specialised just below) and the Grothendieck hypothesis (Tag 079P,
`Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian`); countable products
are not exact in a general Grothendieck abelian category, so neither hypothesis implies the
other. -/
theorem exists_map_bijective_Qh_of_exists_quasiIso_isKInjective
    (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      QuasiIso f ∧ I.IsKInjective) (Y : DerivedCategory A) :
    ∃ I : HomotopyCategory A (ComplexShape.up ℤ), ∃ _e : DerivedCategory.Qh.obj I ≅ Y,
      ∀ X : HomotopyCategory A (ComplexShape.up ℤ),
        Function.Bijective (DerivedCategory.Qh.map : (X ⟶ I) → _) := by
  obtain ⟨I, f, hf, hI⟩ := hres (DerivedCategory.Q.objPreimage Y)
  exact ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I,
    (DerivedCategory.quotientCompQhIso A).app I ≪≫
      (asIso (DerivedCategory.Q.map f)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso Y,
    fun X => CochainComplex.IsKInjective.Qh_map_bijective X I⟩

variable [EnoughInjectives A] [HasProductsOfShape ℕ A] [HasExactLimitsOfShape (Discrete ℕ) A]

/-- Every object of `D(A)` is the image under `Qh` of a K-injective complex, and `Qh` is bijective
on the morphism sets into it. -/
theorem exists_map_bijective_Qh (Y : DerivedCategory A) :
    ∃ I : HomotopyCategory A (ComplexShape.up ℤ), ∃ _e : DerivedCategory.Qh.obj I ≅ Y,
      ∀ X : HomotopyCategory A (ComplexShape.up ℤ),
        Function.Bijective (DerivedCategory.Qh.map : (X ⟶ I) → _) :=
  exists_map_bijective_Qh_of_exists_quasiIso_isKInjective A
    (fun K => by
      obtain ⟨I, f, hf, hI⟩ := CochainComplex.exists_quasiIso_isKInjective K
      exact ⟨I, f, hf, hI⟩) Y

/-- **Stacks Tag 0A5L** for an arbitrary index type. If `A` has enough injectives and exact
countable products, then `Q : C(A) ⥤ D(A)` preserves coproducts of every shape available in `A`,
with no countability restriction on the shape. -/
theorem derivedCategory_Q_preservesCoproductsOfShape_of_enoughInjectives
    (J : Type t) [HasCoproductsOfShape J A] :
    PreservesColimitsOfShape (Discrete J) (DerivedCategory.Q (C := A)) := by
  have hK (K : J → CochainComplex A ℤ) :
      PreservesColimit (Discrete.functor K) (DerivedCategory.Q (C := A)) := by
    set q := HomotopyCategory.quotient A (ComplexShape.up ℤ) with hq
    have hc := (isColimit_mapCofan_of_exists_map_bijective DerivedCategory.Qh
      (exists_map_bijective_Qh A) (fun j => q.map (Sigma.ι K j))
      (HomotopyCategoryCoproduct.cleanColimit A K)).some
    have : PreservesColimit (Discrete.functor K) (q ⋙ DerivedCategory.Qh) :=
      preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct K)
        ((isColimitMapCoconeCofanMkEquiv (q ⋙ DerivedCategory.Qh) K (Sigma.ι K)).symm hc)
    exact preservesColimit_of_natIso _ (DerivedCategory.quotientCompQhIso A)
  have := hK
  exact preservesColimitsOfShape_of_discrete _

end ArbitraryShape
