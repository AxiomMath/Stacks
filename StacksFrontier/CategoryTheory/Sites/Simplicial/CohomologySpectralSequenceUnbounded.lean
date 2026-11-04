module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.CohomologySpectralSequence
public import StacksFrontier.CategoryTheory.Sites.Simplicial.VanishingCohomology

/-!
# The unbounded cohomology spectral sequence of a simplicial site

Let `S` be a simplicial-site situation (Stacks 09WE), with total site `C_total` and component
sites `C_p`, and let `K` be an object of the unbounded derived category `D(C_total)` of abelian
sheaves on the total site, represented by a K-injective complex `I^•`. Stacks 0H0V constructs the
spectral sequence of the filtration by the simplicial coordinate of the product totalization
`Tot_π(A^{•,•})` of the double complex `A^{p,q} = Γ(C_p, I^q_p)`, and asserts two
identifications:

```
E_1^{p,q} = H^q(C_p, K_p),          Tot_π(A^{•,•}) = RΓ(C_total, K).
```

The spectral sequence itself, with `E_0^{p,q} = Γ(C_p, I^q_p)` and `E_1^{p,q} =
H^q(Γ(C_p, I^•_p))`, is
`CategoryTheory.SimplicialSiteSituation.sectionsProductSpectralSequence` and its two page
identifications in
`StacksFrontier/CategoryTheory/Sites/Simplicial/CohomologySpectralSequence.lean`. This file supplies
the two identifications above, which that file records as missing.

Both rest on the same comparison. The double complex `A^{p,q} = Γ(C_p, I^q_p)` of the complex of
Stacks 0D77 is, column by column, the double complex `Hom(P_p, I^q)` of the integral resolution
`P : … → g_{2!}Z → g_{1!}Z → g_{0!}Z` of Stacks 09WI, by the adjunction identification
`Hom(g_{p!}Z, F) = Γ(C_p, F_p)`; this is `sectionsProductDoubleComplexIsoHom`. Hence

* its `p`-th column is `Hom(Z_{C_p}, I^•_p)`, whose cohomology is `H^q(C_p, K_p)` because `I^•_p`
  is K-injective (Stacks 09WH); and
* its product totalization is the Hom complex out of `P` placed in non-positive degrees
  (`CochainComplex.homProductTotalIso`), which `P → Z[0]` being a quasi-isomorphism and `I^•`
  being K-injective identifies with `Hom(Z, I^•) = Γ(C_total, I^•) = RΓ(C_total, K)`.

Cohomology is written in its derived-Hom form, as in
`StacksFrontier/CategoryTheory/Sites/Simplicial/VanishingCohomology.lean`: `H^i(C, K)` is the group
of morphisms from the constant integer sheaf of `C`, placed in degree `0`, to `K[i]` in the
unbounded derived category, and `K_p` is `componentRestrictionDerived S ⦋p⦌` applied to `K`. This
is the source's own first equality `RΓ(C_total, K) = R Hom(Z, K)`, which "holds in any site".

## Main definitions

* `HomologicalComplex₂.productTotalFunctor`: the product totalization of a double complex of
  abelian groups whose first index runs over `ℕ`, as a functor.
* `CategoryTheory.SimplicialSiteSituation.sectionsProductDoubleComplexIsoHom`: the double complex
  `A^{p,q} = Γ(C_p, Z^q_p)` is the double complex `Hom(P_p, Z^q)` of the integral resolution of
  Stacks 09WI.
* `CategoryTheory.SimplicialSiteSituation.totalSectionsToProductTotal`: the comparison
  `Γ(C_total, I^•) ⟶ Tot_π(A^{•,•})`.

## Main results

* `CategoryTheory.SimplicialSiteSituation.sectionsProductSpectralSequencePageOneAddEquiv`:
  **Stacks 0H0V**, `E_1^{p,q} = H^q(C_p, K_p)`.
* `CategoryTheory.SimplicialSiteSituation.quasiIso_totalSectionsToProductTotal` and
  `CategoryTheory.SimplicialSiteSituation.sectionsProductTotalHomologyAddEquiv`:
  **Stacks 0H0V**, `Tot_π(A^{•,•}) = RΓ(C_total, K)`, as a quasi-isomorphism of complexes and
  degreewise on cohomology.

## Carried hypotheses

None. The integral resolution of Stacks 09WI once took as an assumption the identification of
the summand inclusions of Stacks 09WG (6) on underlying sheaves of sets; that identification is
proved for an arbitrary simplicial-site situation by
`CategoryTheory.SimplicialSiteSituation.summandForgetCompatibility`, so neither the resolution
nor the complex of Stacks 0D77 built from it carries a hypothesis, and nor does anything here.
No boundedness hypothesis appears either: `I^•` is only asked to be K-injective, which is
exactly what the source asks.

## References

* [Stacks Project, Tag 0H0V](https://stacks.math.columbia.edu/tag/0H0V)
* [Stacks Project, Tag 09WI](https://stacks.math.columbia.edu/tag/09WI)
* [Stacks Project, Tag 09WH](https://stacks.math.columbia.edu/tag/09WH)
* [Stacks Project, Tag 0D77](https://stacks.math.columbia.edu/tag/0D77)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

/-! ### The product totalization as a functor -/

namespace HomologicalComplex₂

variable {K L M : HomologicalComplex₂ AddCommGrpCat.{u} (ComplexShape.up ℕ) (ComplexShape.up ℤ)}

/-- The degree-`n` term of the map of product total complexes induced by a map of double
complexes: the component in column `p` and row `q` is the component of the map. -/
def productTotalXMap (φ : K ⟶ L) (n : ℤ) : K.productTotalX n ⟶ L.productTotalX n :=
  AddCommGrpCat.ofHom
    { toFun x i := (φ.f i.1.1).f i.1.2 (x i)
      map_zero' := funext fun _ => map_zero _
      map_add' _ _ := funext fun _ => map_add _ _ _ }

/-- The component of the map of product total complexes in column `p` and row `q` is the
component of the map of double complexes. -/
@[simp]
lemma productTotalXMap_apply (φ : K ⟶ L) (n : ℤ) (x : K.productTotalX n)
    (i : {pq : ℕ × ℤ // (pq.1 : ℤ) + pq.2 = n}) :
    productTotalXMap φ n x i = (φ.f i.1.1).f i.1.2 (x i) :=
  rfl

private lemma hom_f_d_apply (φ : K ⟶ L) (p : ℕ) (q q' : ℤ) (x : (K.X p).X q) :
    (φ.f p).f q' ((K.X p).d q q' x) = (L.X p).d q q' ((φ.f p).f q x) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, (φ.f p).comm]

private lemma hom_d_f_apply (φ : K ⟶ L) (p p' : ℕ) (q : ℤ) (x : (K.X p).X q) :
    (φ.f p').f q ((K.d p p').f q x) = (L.d p p').f q ((φ.f p).f q x) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, φ.comm]

/-- The map of product total complexes commutes with the differentials. -/
lemma productTotalXMap_comm (φ : K ⟶ L) (n : ℤ) :
    productTotalXMap φ n ≫ L.productTotalD n =
      K.productTotalD n ≫ productTotalXMap φ (n + 1) := by
  ext x
  funext i
  obtain ⟨⟨p, q⟩, h⟩ := i
  change L.productTotalDComp n (productTotalXMap φ n x) p q h =
    (φ.f p).f q (K.productTotalDComp n x p q h)
  cases p with
  | zero =>
    rw [productTotalDComp_zero_left, productTotalDComp_zero_left]
    exact (hom_f_d_apply φ 0 (q - 1) q _).symm
  | succ p =>
    rw [productTotalDComp_succ, productTotalDComp_succ, map_add, map_zsmul]
    rw [hom_d_f_apply φ p (p + 1) q, hom_f_d_apply φ (p + 1) (q - 1) q]
    simp only [productTotalXMap_apply]

/-- **The product totalization of a double complex of abelian groups whose first index runs over
`ℕ`, as a functor.** -/
@[simps obj]
def productTotalFunctor :
    HomologicalComplex₂ AddCommGrpCat.{u} (ComplexShape.up ℕ) (ComplexShape.up ℤ) ⥤
      CochainComplex AddCommGrpCat.{u} ℤ where
  obj K := K.productTotal
  map {K L} φ :=
    { f := productTotalXMap φ
      comm' := by
        intro i j hij
        obtain rfl : i + 1 = j := hij
        rw [productTotal_d, productTotal_d]
        exact productTotalXMap_comm φ i }
  map_id K := by
    apply HomologicalComplex.hom_ext
    intro n
    ext x
    rfl
  map_comp {K L M} φ ψ := by
    apply HomologicalComplex.hom_ext
    intro n
    ext x
    rfl

end HomologicalComplex₂

namespace CategoryTheory.SimplicialSiteSituation

attribute [local instance] HasDerivedCategory.standard

variable (S : SimplicialSiteSituation.{u})
  (Z : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ)

/-! ### The double complex of sections is the Hom double complex of the integral resolution -/

/-- **The `p`-th column of the double complex `A^{p,q} = Γ(C_p, Z^q_p)` is the complex
`Hom(g_{p!}Z, Z^•)`**: the adjunction identification `Hom(g_{p!}Z, F) = Γ(C_p, F_p)` of the proof
of Stacks 0D77, applied in each degree of `Z^•`. -/
def sectionsProductColumnIsoHom (p : ℕ) :
    (CochainComplex.homProductDoubleComplex S.simplicialIntegerComplex Z).X p ≅
      (S.sectionsProductDoubleComplex Z).X p :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q => (S.resolutionTermSectionsIso p).app (Z.X q))
    fun q q' _ => ((S.resolutionTermSectionsIso p).hom.naturality (Z.d q q')).symm

/-- In degree `q`, the isomorphism `sectionsProductColumnIsoHom` is the adjunction
identification `Hom(g_{p!}Z, Z^q) = Γ(C_p, Z^q_p)`. -/
@[simp]
lemma sectionsProductColumnIsoHom_hom_f (p : ℕ) (q : ℤ) :
    (S.sectionsProductColumnIsoHom Z p).hom.f q =
      (S.resolutionTermSectionsIso p).hom.app (Z.X q) :=
  rfl

/-- The horizontal differential of the double complex `Hom(P_p, Z^q)` of the integral resolution
is precomposition with the differential of the resolution. -/
lemma homProductDoubleComplex_d_f (p : ℕ) (q : ℤ) :
    ((CochainComplex.homProductDoubleComplex
          S.simplicialIntegerComplex Z).d p (p + 1)).f q =
      (S.resolutionHomDifferential p).app (Z.X q) := by
  rw [CochainComplex.homProductDoubleComplex_d]
  rfl

/-- The horizontal differential of the double complex `A^{p,q} = Γ(C_p, Z^q_p)` is the
differential of the complex of Stacks 0D77. -/
lemma sectionsProductDoubleComplex_d_f (p : ℕ) (q : ℤ) :
    ((S.sectionsProductDoubleComplex Z).d p (p + 1)).f q =
      (S.sectionsDifferential p).app (Z.X q) :=
  S.cechSectionsComplex_obj_d (Z.X q) p

/-- **The double complex `A^{p,q} = Γ(C_p, Z^q_p)` of Stacks 0H0V is the double complex
`Hom(P_p, Z^q)` of the integral resolution `P` of Stacks 09WI.**

Column by column this is the adjunction identification `Hom(g_{p!}Z, F) = Γ(C_p, F_p)`; the
horizontal differentials agree because the differential of the complex of Stacks 0D77 is by
construction precomposition with the differential of `P`, transported along that
identification. -/
def sectionsProductDoubleComplexIsoHom :
    CochainComplex.homProductDoubleComplex S.simplicialIntegerComplex Z ≅
      S.sectionsProductDoubleComplex Z :=
  HomologicalComplex.Hom.isoOfComponents (S.sectionsProductColumnIsoHom Z)
    fun p p' hpp' => by
      obtain rfl : p + 1 = p' := hpp'
      apply HomologicalComplex.hom_ext
      intro q
      rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
        S.sectionsProductDoubleComplex_d_f Z p q,
        S.homProductDoubleComplex_d_f Z p q,
        S.sectionsProductColumnIsoHom_hom_f Z p q,
        S.sectionsProductColumnIsoHom_hom_f Z (p + 1) q]
      exact NatTrans.congr_app
        (S.resolutionTermSectionsIso_hom_comp_sectionsDifferential p) (Z.X q)

/-! ### The first page is the cohomology of the components -/

/-- **The `p`-th column of the double complex `A^{p,q} = Γ(C_p, Z^q_p)` is the complex
`Hom(Z_{C_p}, Z^•_p)`** of morphisms from the constant integer sheaf of the component site into
the restriction of `Z^•`. -/
def sectionsProductColumnIsoCoyoneda (p : ℕ) :
    (S.sectionsProductDoubleComplex Z).X p ≅
      CochainComplex.coyonedaComplex (integerSheaf (S.componentTopology ⦋p⦌))
        (((S.restrictAb ⦋p⦌).mapHomologicalComplex (ComplexShape.up ℤ)).obj Z) :=
  (S.sectionsProductColumnIsoHom Z p).symm ≪≫
    S.integerResolutionColumnIso p Z

/-- **Stacks 0H0V, the first page: `E_1^{p,q} = H^q(C_p, K_p)`.** For `I^•` a K-injective complex
of abelian sheaves on the total site representing `K` in `D(C_total)`, the first page of the
spectral sequence of the filtration by the simplicial coordinate of the product totalization of
`A^{p,q} = Γ(C_p, I^q_p)` is the cohomology of the component site `C_p` of the restriction `K_p`.

No boundedness hypothesis is made on `I^•`, as in the source. Cohomology is written in its
derived-Hom form, and `K_p` is the restriction of `K = Q(I^•)` to the component in simplicial
degree `p`; the proof uses that restriction to a component preserves K-injectivity, which is
Stacks 09WH. -/
@[stacks 0H0V "the first page of the spectral sequence is `H^q(C_p, K_p)`, for a complex that is
not bounded below"]
def sectionsProductSpectralSequencePageOneAddEquiv
    (I : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ) [I.IsKInjective] (p : ℕ) (q : ℤ) :
    (((S.sectionsProductSpectralSequence I).page 1 zero_le_one).X ((p : ℤ), q)) ≃+
      ((DerivedCategory.singleFunctor (Sheaf (S.componentTopology ⦋p⦌) Ab.{u}) 0).obj
          (integerSheaf (S.componentTopology ⦋p⦌)) ⟶
        ((S.componentRestrictionDerived ⦋p⦌).obj (DerivedCategory.Q.obj I))⟦q⟧) :=
  haveI := isKInjective_componentRestriction S ⦋p⦌ I
  (((S.sectionsProductDoubleComplex I).productTotalColumnOnePageIso p q ≪≫
        HomologicalComplex.homologyMapIso
          (S.sectionsProductColumnIsoCoyoneda I p) q).addCommGroupIsoToAddEquiv.trans
      (CochainComplex.coyonedaComplexHomologyEquiv (integerSheaf (S.componentTopology ⦋p⦌))
        (((S.restrictAb ⦋p⦌).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) q)).trans
    (Linear.homCongr ℤ
      (Iso.refl ((DerivedCategory.singleFunctor (Sheaf (S.componentTopology ⦋p⦌) Ab.{u}) 0).obj
        (integerSheaf (S.componentTopology ⦋p⦌))))
      ((shiftFunctor (DerivedCategory (Sheaf (S.componentTopology ⦋p⦌) Ab.{u})) q).mapIso
        ((S.restrictAb ⦋p⦌).mapDerivedCategoryFactors.app I).symm)).toAddEquiv

/-! ### The product totalization is the derived global sections -/

/-- **The product totalization `Tot_π(A^{•,•})` of `A^{p,q} = Γ(C_p, Z^q_p)` is the Hom complex
out of the integral resolution of Stacks 09WI**, placed in non-positive degrees. -/
def sectionsProductTotalIsoHomComplex :
    CochainComplex.HomComplex
        (S.simplicialIntegerComplex.extend ComplexShape.embeddingDownNat) Z ≅
      S.sectionsProductTotal Z :=
  CochainComplex.homProductTotalIso S.simplicialIntegerComplex Z ≪≫
    HomologicalComplex₂.productTotalFunctor.mapIso (S.sectionsProductDoubleComplexIsoHom Z)

/-- The complex of global sections `Γ(C_total, Z^•)` is the complex `Hom(Z, Z^•)` of morphisms
from the constant integer sheaf. -/
def totalSectionsComplexIsoCoyoneda :
    ((Sheaf.Γ S.totalTopology Ab.{u}).mapHomologicalComplex (ComplexShape.up ℤ)).obj Z ≅
      CochainComplex.coyonedaComplex S.totalIntegerSheaf Z :=
  ((NatIso.mapHomologicalComplex (integerHomIsoGlobalSections S.totalTopology)
    (ComplexShape.up ℤ)).app Z).symm

/-- **The comparison `Γ(C_total, Z^•) ⟶ Tot_π(A^{•,•})`**: the global sections complex, read as
the Hom complex out of the constant integer sheaf placed in degree zero, mapped by precomposition
with the augmentation of the integral resolution of Stacks 09WI, read through
`sectionsProductTotalIsoHomComplex`. -/
def totalSectionsToProductTotal :
    CochainComplex.coyonedaComplex S.totalIntegerSheaf Z ⟶ S.sectionsProductTotal Z :=
  (Stacks.Cohomology.Locality.homComplexSingleIsoCoyoneda S.totalIntegerSheaf Z).inv ≫
    CochainComplex.HomComplex.homComplexMap S.integerCochainAugmentation (𝟙 Z) ≫
      (S.sectionsProductTotalIsoHomComplex Z).hom

/-- **Stacks 0H0V, `Tot_π(A^{•,•}) = RΓ(C_total, K)`.** For `I^•` a K-injective complex of
abelian sheaves on the total site, the comparison from the complex of global sections
`Γ(C_total, I^•)` — which is `RΓ(C_total, K)` for `K = Q(I^•)` — to the product totalization of
`A^{p,q} = Γ(C_p, I^q_p)` is a quasi-isomorphism.

This is the source's chain of equalities. The global sections complex is the Hom complex out of
the constant integer sheaf `Z`, which is `R Hom(Z, K)`; the integral resolution
`… → g_{2!}Z → g_{1!}Z → g_{0!}Z` of Stacks 09WI resolves `Z`, so for the K-injective target
`I^•` the Hom complex out of it computes the same thing; and that Hom complex is the product
totalization of `A^{p,q} = Hom(g_{p!}Z, I^q) = Γ(C_p, I^q_p)`. No boundedness hypothesis is made
on `I^•`: K-injectivity is what replaces it. -/
@[stacks 0H0V "`Tot_π(A^{•,•}) = RΓ(C_total, K)` for a K-injective representative, as a
quasi-isomorphism of complexes"]
instance quasiIso_totalSectionsToProductTotal
    (I : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ) [I.IsKInjective] :
    QuasiIso (S.totalSectionsToProductTotal I) := by
  haveI := CochainComplex.HomComplex.homComplexMap_quasiIso
    S.integerCochainAugmentation (𝟙 I)
  dsimp only [totalSectionsToProductTotal]
  infer_instance

/-- **Stacks 0H0V, `Tot_π(A^{•,•}) = RΓ(C_total, K)` degreewise on cohomology**:
`H^n(Tot_π(A^{•,•})) = H^n(C_total, K)`.

Cohomology is written in its derived-Hom form, so the right-hand side is literally the source's
`R Hom(Z, K)` in degree `n`, which is `RΓ(C_total, K)` because the first equality of the source
"holds in any site". -/
@[stacks 0H0V "`H^n(Tot_π(A^{•,•})) = H^n(C_total, K)` for a K-injective representative"]
def sectionsProductTotalHomologyAddEquiv
    (I : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ) [I.IsKInjective] (n : ℤ) :
    ((S.sectionsProductTotal I).homology n) ≃+
      ((DerivedCategory.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).obj S.totalIntegerSheaf ⟶
        (DerivedCategory.Q.obj I)⟦n⟧) :=
  haveI : IsIso (HomologicalComplex.homologyMap
      (S.totalSectionsToProductTotal I) n) := by
    have := (S.quasiIso_totalSectionsToProductTotal I).quasiIsoAt n
    rwa [_root_.quasiIsoAt_iff_isIso_homologyMap] at this
  ((asIso (HomologicalComplex.homologyMap
        (S.totalSectionsToProductTotal I) n)).symm).addCommGroupIsoToAddEquiv.trans
    (CochainComplex.coyonedaComplexHomologyEquiv S.totalIntegerSheaf I n)

/-- **The comparison `Γ(C_total, Z^•) ⟶ Tot_π(A^{•,•})` out of the complex of global sections
itself**, the shape in which the source states the equality. -/
def globalSectionsToProductTotal :
    ((Sheaf.Γ S.totalTopology Ab.{u}).mapHomologicalComplex (ComplexShape.up ℤ)).obj Z ⟶
      S.sectionsProductTotal Z :=
  (S.totalSectionsComplexIsoCoyoneda Z).hom ≫ S.totalSectionsToProductTotal Z

/-- **Stacks 0H0V, `Γ(C_total, I^•) = Tot_π(A^{•,•})`.** For `I^•` a K-injective complex of
abelian sheaves on the total site, the comparison from its complex of global sections to the
product totalization of `A^{p,q} = Γ(C_p, I^q_p)` is a quasi-isomorphism. This is the previous
statement with its source written as the complex of global sections rather than as the Hom
complex out of the constant integer sheaf. -/
@[stacks 0H0V "`Γ(C_total, I^•) = Tot_π(A^{•,•})` for a K-injective complex, as a
quasi-isomorphism of complexes"]
instance quasiIso_globalSectionsToProductTotal
    (I : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ) [I.IsKInjective] :
    QuasiIso (S.globalSectionsToProductTotal I) := by
  dsimp only [globalSectionsToProductTotal]
  infer_instance

/-! ### The spectral sequence of an arbitrary object of the unbounded derived category -/

/-- **Stacks 0H0V, the spectral sequence of an object `K` of `D(C_total)` with no boundedness
hypothesis**: the spectral sequence of
`CategoryTheory.SimplicialSiteSituation.sectionsProductSpectralSequence` for the chosen
K-injective complex with injective terms representing `K`. -/
@[stacks 0H0V "the spectral sequence of an arbitrary object of the unbounded derived category of
the total site"]
abbrev unboundedSpectralSequence (K : DerivedCategory (Sheaf S.totalTopology Ab.{u})) :
    CohomologicalSpectralSequence Ab.{u} 0 :=
  S.sectionsProductSpectralSequence (S.totalKInjectiveModel K)

/-- **Stacks 0H0V, the first page: `E_1^{p,q} = H^q(C_p, K_p)`** for an arbitrary object `K` of
`D(C_total)`.

The first differential of the first page of a cohomological spectral sequence has bidegree
`(1, 0)` by construction, so under this identification it is a map
`H^q(C_p, K_p) → H^q(C_{p + 1}, K_{p + 1})`, as the source's reference to Stacks 09WJ asks. -/
@[stacks 0H0V "the first page is `E_1^{p,q} = H^q(C_p, K_p)`, for an arbitrary object of the
unbounded derived category of the total site"]
def unboundedSpectralSequencePageOneAddEquiv
    (K : DerivedCategory (Sheaf S.totalTopology Ab.{u})) (p : ℕ) (q : ℤ) :
    (((S.unboundedSpectralSequence K).page 1 zero_le_one).X ((p : ℤ), q)) ≃+
      ((DerivedCategory.singleFunctor (Sheaf (S.componentTopology ⦋p⦌) Ab.{u}) 0).obj
          (integerSheaf (S.componentTopology ⦋p⦌)) ⟶
        ((S.componentRestrictionDerived ⦋p⦌).obj K)⟦q⟧) :=
  (S.sectionsProductSpectralSequencePageOneAddEquiv (S.totalKInjectiveModel K) p q).trans
    (Linear.homCongr ℤ
      (Iso.refl ((DerivedCategory.singleFunctor (Sheaf (S.componentTopology ⦋p⦌) Ab.{u}) 0).obj
        (integerSheaf (S.componentTopology ⦋p⦌))))
      ((shiftFunctor (DerivedCategory (Sheaf (S.componentTopology ⦋p⦌) Ab.{u})) q).mapIso
        ((S.componentRestrictionDerived ⦋p⦌).mapIso (S.totalKInjectiveModelIso K)))).toAddEquiv

/-- **Stacks 0H0V, `Tot_π(A^{•,•}) = RΓ(C_total, K)`** for an arbitrary object `K` of
`D(C_total)`, degreewise on cohomology. -/
@[stacks 0H0V "`H^n(Tot_π(A^{•,•})) = H^n(C_total, K)` for an arbitrary object of the unbounded
derived category of the total site"]
def unboundedProductTotalHomologyAddEquiv
    (K : DerivedCategory (Sheaf S.totalTopology Ab.{u})) (n : ℤ) :
    ((S.sectionsProductTotal (S.totalKInjectiveModel K)).homology n) ≃+
      ((DerivedCategory.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).obj S.totalIntegerSheaf ⟶
        K⟦n⟧) :=
  (S.sectionsProductTotalHomologyAddEquiv (S.totalKInjectiveModel K) n).trans
    (Linear.homCongr ℤ
      (Iso.refl ((DerivedCategory.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).obj
        S.totalIntegerSheaf))
      ((shiftFunctor (DerivedCategory (Sheaf S.totalTopology Ab.{u})) n).mapIso
        (S.totalKInjectiveModelIso K))).toAddEquiv

end CategoryTheory.SimplicialSiteSituation

end
