module

public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleShriekFiniteGeneration
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleShriekPresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Adjunction

/-!
# Covering one constructible cohomology sheaf by extensions by zero

Let `X` be a quasi-compact and quasi-separated scheme, let `Λ` be a Noetherian ring, let
`K ∈ D(X_étale, Λ)` and let `b` be an integer for which `H^b(K)` is constructible. Tag 095Z
asserts that there are a sheaf `F` which is a finite direct sum of sheaves `j_{U!} Λ-underline`
with `U` an affine object of `X_étale`, and a map `F[-b] → K` in `D(X_étale, Λ)` inducing a
surjection `F → H^b(K)`.

The conclusion is an existence statement in the source and is stated as one here.

## Main results

* `Stacks.Homology.exists_single_map_epi_derivedHomology` — a map from a cocycle of a
  cochain complex which is surjective on homology produces a map out of the corresponding
  single-degree complex in the derived category, surjective on cohomology in that degree.
* `Stacks.EtaleCohomology.exists_shriekConstant_cover_of_isConstructible_homology` —
  **Tag 095Z**, with nothing granted.

## Implementation notes

`F[-b]` is `DerivedCategory.singleFunctor` in degree `b`, the sheaf `F` placed in
degree `b`; `H^b` is `DerivedCategory.homologyFunctor` in degree `b`, which is
what `Stacks.EtaleCohomology.IsConstructible` of Tag 095W uses, and the map induced on `H^b` is
the image of the morphism under that functor. The source says the induced map `F → H^b(K)` is
surjective, which is this map after the canonical identification `H^b(F[-b]) ≅ F`; the statement
below asserts surjectivity of the map between the cohomology objects, which carries the same
content and needs no identification to state. The derived category is the standard model, the
model at which `Stacks.EtaleCohomology.IsConstructible` is stated.

`j_{U!} Λ-underline` is `AlgebraicGeometry.moduleShriekConstant`, the extension by zero along
`U ⟶ X` of the constant sheaf with value the free rank-one `Λ`-module, at the coefficient
universe `ModuleCat.{max (u + 1) r} Λ` that extension by zero forces.

The derived-category half is proved here and is unconditional. It is the half the source
performs silently: a complex `A` representing `K` is chosen —
`DerivedCategory.Q.objPreimage` — its degree-`b` cocycles `Z^b(A)` carry the
canonical surjection onto `H^b(K)`, a map `F ⟶ Z^b(A)` surjective after that projection extends
to a chain map `F[-b] ⟶ A` by `HomologicalComplex.mkHomFromSingle`, and the degree-`b` homology
of that chain map is surjective; the comparison
`DerivedCategory.homologyFunctorFactors` transports this to the derived category, and
`DerivedCategory.singleFunctorIsoCompQ` identifies the source. None of this uses the étale site,
so it is stated for an arbitrary abelian category.

### What the proof rests on

Nothing is carried. The sheaf-theoretic half is the conjunction of the two results the
source's proof quotes, in exactly the shape it quotes them: Modules on Sites Tag 093B produces a
surjection `⊕_{i ∈ I} j_{U_i!} Λ-underline → 𝒵` onto the sheaf of cocycles with all `U_i`
affine, and Tag 095P then produces a finite subset `I' ⊆ I` for which the image of
`⊕_{i ∈ I'}` in the constructible sheaf `H^b(K)` is already everything. Their conjunction — for
a constructible sheaf `ℋ` and any surjection `p : 𝒵 → ℋ`, finitely many affine objects and a map
`⊕ j_{U_i!} Λ-underline → 𝒵` suffice for `p` to stay surjective — is
`AlgebraicGeometry.exists_finite_epi_comp_sigma_moduleShriekConstant_affine`, assembled from
`AlgebraicGeometry.exists_epi_sigma_moduleShriekConstant_affine`, which is Tag 093B part (2) for
sheaves of `Λ`-modules with the generators taken at affine étale objects, and
`AlgebraicGeometry.exists_finset_epi_sigma_desc_of_isConstructibleModuleSheaf`, which is
Tag 095P.

Constructibility of the summands of the presentation, without which the cokernel argument of
Tag 095P does not start, is Tag 03S8 for sheaves of `Λ`-modules,
`AlgebraicGeometry.isConstructibleModuleSheaf_moduleShriekConstant`, which holds at the
coefficient universe `max (u + 1) r` of a ring in a universe `r` of its own: its proof passes
through `AlgebraicGeometry.moduleShriekConstantIsoCopower` and `ModuleCat.copower`, not through
`ModuleCat.free Λ`, whose source `Type r ⥤ ModuleCat.{r} Λ` would tie the two universes together.

## References

* [Stacks Project, Tag 095Z](https://stacks.math.columbia.edu/tag/095Z)
* [Stacks Project, Tag 095W](https://stacks.math.columbia.edu/tag/095W)
* [Stacks Project, Tag 093B](https://stacks.math.columbia.edu/tag/093B)
* [Stacks Project, Tag 095P](https://stacks.math.columbia.edu/tag/095P)
* [Stacks Project, Tag 03S8](https://stacks.math.columbia.edu/tag/03S8)
* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts

universe u r

namespace Stacks.Homology

open DerivedCategory

attribute [local instance] HasDerivedCategory.standard

variable {C : Type*} [Category C] [Abelian C]

/-- A map into the degree-`n` cocycles of a cochain complex extends to a chain map out of the
complex concentrated in degree `n`, and if the map is surjective after projecting to homology
then the extension is surjective on degree-`n` homology. -/
public theorem exists_single_map_epi_homologyMap (K : CochainComplex C ℤ) (n : ℤ) (P : C)
    (f : P ⟶ K.cycles n) (hf : Epi (f ≫ K.homologyπ n)) :
    ∃ φ : (CochainComplex.singleFunctor C n).obj P ⟶ K,
      Epi (HomologicalComplex.homologyMap φ n) := by
  let φ := HomologicalComplex.mkHomFromSingle (f ≫ K.iCycles n) (fun j _ ↦ by simp)
  refine ⟨φ, ?_⟩
  have hcycles : HomologicalComplex.cyclesMap φ n =
      (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) n P).hom ≫ f := by
    apply (cancel_mono (K.iCycles n)).1
    simp [φ, HomologicalComplex.cyclesMap_i,
      HomologicalComplex.singleObjCyclesSelfIso_hom, Category.assoc]
  have h : ((CochainComplex.singleFunctor C n).obj P).homologyπ n ≫
      HomologicalComplex.homologyMap φ n =
      (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) n P).hom ≫
        (f ≫ K.homologyπ n) := by
    rw [HomologicalComplex.homologyπ_naturality, hcycles, Category.assoc]
  have : Epi (((CochainComplex.singleFunctor C n).obj P).homologyπ n ≫
      HomologicalComplex.homologyMap φ n) := by
    rw [h]; exact epi_comp _ _
  exact epi_of_epi (((CochainComplex.singleFunctor C n).obj P).homologyπ n) _

/-- Let `K` be an object of the derived category, `A` a cochain complex representing it and `P`
an object admitting a map to the degree-`n` cocycles of `A` which is surjective after projecting
to homology. Then there is a map `P[-n] ⟶ K` in the derived category which is surjective on
degree-`n` cohomology. -/
public theorem exists_single_map_epi_derivedHomology (K : DerivedCategory C)
    (A : CochainComplex C ℤ) (e : Q.obj A ≅ K) (n : ℤ) (P : C) (f : P ⟶ A.cycles n)
    (hf : Epi (f ≫ A.homologyπ n)) :
    ∃ g : (singleFunctor C n).obj P ⟶ K, Epi ((homologyFunctor C n).map g) := by
  obtain ⟨α, hα⟩ := exists_single_map_epi_homologyMap A n P f hf
  refine ⟨((singleFunctorIsoCompQ C n).app P).hom ≫ Q.map α ≫ e.hom, ?_⟩
  have hQ : Epi ((homologyFunctor C n).map (Q.map α)) := by
    refine (epi_comp_iff_of_isIso _ ((homologyFunctorFactors C n).hom.app A)).mp ?_
    rw [homologyFunctorFactors_hom_naturality α n]
    exact epi_comp' inferInstance hα
  rw [Functor.map_comp, Functor.map_comp]
  exact epi_comp' inferInstance (epi_comp' hQ inferInstance)

end Stacks.Homology

namespace Stacks.EtaleCohomology

open _root_.AlgebraicGeometry DerivedCategory

attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]

/-- **Stacks 095Z.** Let `X` be a quasi-compact and quasi-separated scheme, let `Λ` be a
Noetherian ring, let `K ∈ D(X_étale, Λ)` and let `b` be an integer for which `H^b(K)` is
constructible. Then there are finitely many affine objects `U i` of the small étale site of `X`
and a map `F[-b] ⟶ K`, where `F = ⊕ᵢ j_{U i!} Λ-underline`, inducing a surjection on degree-`b`
cohomology.

A complex `A` representing `K` is chosen;
`AlgebraicGeometry.exists_finite_epi_comp_sigma_moduleShriekConstant_affine` — Tags 093B and
095P in the shape the source's proof quotes them — covers the degree-`b` cocycles of `A` well
enough for the canonical surjection onto `H^b(K)` to survive, and
`Stacks.Homology.exists_single_map_epi_derivedHomology` turns that cover into the
required map in the derived category.

Nothing is granted; see "What the proof rests on" in the module documentation. -/
@[stacks 095Z]
public theorem exists_shriekConstant_cover_of_isConstructible_homology (X : B.Scheme)
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    [HasSheafify (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)]
    [∀ (S T : B.Scheme) (g : T ⟶ S),
      ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{max (u + 1) r} Λ)
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
      HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
        (ModuleCat.{max (u + 1) r} Λ)]
    (K : DerivedCategory (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) r} Λ))) (b : ℤ)
    (hK : IsConstructibleModuleSheaf B X Λ
      ((homologyFunctor (Sheaf (SmallEtale.topology B X.obj X.property)
        (ModuleCat.{max (u + 1) r} Λ)) b).obj K)) :
    ∃ (n : ℕ) (U : Fin n → SmallEtale B X.obj X.property),
      (∀ i, IsAffine ((SmallEtale.toScheme B X.obj X.property).obj (U i))) ∧
      ∃ f : (singleFunctor (Sheaf (SmallEtale.topology B X.obj X.property)
          (ModuleCat.{max (u + 1) r} Λ)) b).obj
          (∐ fun i : Fin n ↦ moduleShriekConstant.{u, r, r} B X Λ (U i)) ⟶ K,
        Epi ((homologyFunctor (Sheaf (SmallEtale.topology B X.obj X.property)
          (ModuleCat.{max (u + 1) r} Λ)) b).map f) := by
  let C := Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)
  let A : CochainComplex C ℤ := Q.objPreimage K
  let e : Q.obj A ≅ K := Q.objObjPreimageIso K
  let eH : A.homology b ≅ (homologyFunctor C b).obj K :=
    ((homologyFunctorFactors C b).app A).symm ≪≫ (homologyFunctor C b).mapIso e
  let p : A.cycles b ⟶ (homologyFunctor C b).obj K := A.homologyπ b ≫ eH.hom
  have : Epi p := epi_comp' inferInstance inferInstance
  obtain ⟨n, U, hU, f, hf⟩ :=
    exists_finite_epi_comp_sigma_moduleShriekConstant_affine B X Λ p hK
  refine ⟨n, U, hU, ?_⟩
  refine Stacks.Homology.exists_single_map_epi_derivedHomology K A e b _ f ?_
  refine (epi_comp_iff_of_isIso (f ≫ A.homologyπ b) eH.hom).mp ?_
  simpa only [p, Category.assoc] using hf

end Stacks.EtaleCohomology

end
