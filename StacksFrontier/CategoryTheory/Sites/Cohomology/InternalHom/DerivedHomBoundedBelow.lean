module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.Algebra.Homology.Resolution.InjectiveResolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedInternalHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplexBoundedBelow

/-!
# The derived internal Hom out of a bounded-above object into a bounded-below one on a site

Let `(C, O)` be a ringed site, let `K` be an object of `D(O)` whose cohomology vanishes in
degrees above `d` and let `L` be an object of `D(O)` whose cohomology vanishes in degrees below
`b`. Then `RSheafHom(K, L)` has no cohomology below `b - d`.

The bound is read on models. The object `K` is represented by a complex `P` concentrated in
degrees `≤ d`, and `L` by a K-injective complex `J` concentrated in degrees `≥ b`; on those
representatives the derived internal Hom is the internal Hom complex `SheafHom(P, J)`, which is
concentrated in degrees `≥ b - d` on the nose by
`AlgebraicGeometry.RingedSite.isStrictlyGE_sheafHomComplex`.

## Main results

* `AlgebraicGeometry.RingedSite.isGE_derivedSheafHom`: the bound `b - d`.
* `AlgebraicGeometry.RingedSite.isLE_derivedSheafHom`: the dual bound `d - e`, out of an object
  with no cohomology below `e` into one represented by a K-injective complex concentrated in
  degrees `≤ d`.
* `AlgebraicGeometry.RingedSite.isBoundedBelow_derivedSheafHom`: the unquantified form, that
  `RSheafHom(K, L)` is cohomologically bounded below as soon as `K` is cohomologically bounded
  above and `L` is cohomologically bounded below.

## Implementation notes

This is the ringed-site companion of `Stacks.SheafOfModules.isGE_derivedSheafHom`, which is
stated for a ringed space. The two statements live in different vocabularies — the derived
internal Hom bifunctor of the site and the one of the space are built from different model
comparisons — so neither specialises to the other; what is shared is the argument.

The three site universes and the module universe are equal, as they are for
`AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor` itself: the functorial K-injective
resolution underlying that bifunctor needs sheaves of `O`-modules to be Grothendieck abelian in
the module universe, and the internal Hom complex raises the module universe.

The strictly bounded-below K-injective representative is produced here rather than imported:
the ringed-space file has the same step as a `private` lemma, which by construction is not
available outside it.

## References

* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- A cohomologically bounded-below object of `D(O)` has a K-injective representative which is
concentrated in degrees `≥ b` on the nose. -/
private theorem exists_isStrictlyGE_isKInjective_model_site
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (b : ℤ) (hL : L.IsGE b) :
    ∃ J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ,
      CochainComplex.IsStrictlyGE J b ∧ J.IsKInjective ∧
        Nonempty (DerivedCategory.Q.obj J ≅ L) := by
  have := hL
  obtain ⟨C, hC, ⟨iC⟩⟩ := L.exists_iso_Q_obj_of_isGE b
  have := hC
  obtain ⟨J, -, hJ⟩ := CochainComplex.exists_injectiveResolution_isStrictlyGE b C
  have := hJ
  exact ⟨J.cocomplex, hJ, CochainComplex.isKInjective_of_injective J.cocomplex b,
    ⟨(asIso (DerivedCategory.Q.map J.ι)).symm ≪≫ iC.symm⟩⟩

/-- The derived internal Hom of `K` and `L` is computed by the internal Hom complex of any
representatives of `K` and `L`, the second being K-injective. -/
private theorem nonempty_iso_derivedSheafHom
    {K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {P J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [J.IsKInjective] (eP : K ≅ DerivedCategory.Q.obj P) (eJ : DerivedCategory.Q.obj J ≅ L) :
    Nonempty (DerivedCategory.Q.obj (sheafHomComplex X P J).obj ≅
      ((derivedSheafHomBifunctor X).obj (op K)).obj L) :=
  ⟨(derivedSheafHomComparison X P J).symm ≪≫
    ((derivedSheafHomBifunctor X).mapIso eP.op).app (DerivedCategory.Q.obj J) ≪≫
      ((derivedSheafHomBifunctor X).obj (op K)).mapIso eJ⟩

/-- **The derived internal Hom of a bounded-above object into a bounded-below object is bounded
below.** If the cohomology of `K` vanishes in degrees above `d` and that of `L` vanishes in
degrees below `b`, then the cohomology of `RSheafHom(K, L)` vanishes in degrees below
`b - d`. -/
public theorem isGE_derivedSheafHom
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (d b : ℤ) (hK : K.IsLE d) (hL : L.IsGE b) :
    (((derivedSheafHomBifunctor X).obj (op K)).obj L).IsGE (b - d) := by
  have := hK
  obtain ⟨P, hP, ⟨eP⟩⟩ := K.exists_iso_Q_obj_of_isLE d
  obtain ⟨J, hJ, hJinj, ⟨eJ⟩⟩ := exists_isStrictlyGE_isKInjective_model_site X L b hL
  have := hP
  have := hJ
  have := hJinj
  have hmodel :
      (DerivedCategory.Q.obj (sheafHomComplex X P J).obj).IsGE (b - d) := by
    have := isStrictlyGE_sheafHomComplex X P J d b
    infer_instance
  obtain ⟨iso⟩ := nonempty_iso_derivedSheafHom X eP eJ
  exact DerivedCategory.TStructure.t.isGE_of_iso iso (b - d)

/-- **The derived internal Hom of a bounded-below object into an object of bounded injective
amplitude is bounded above.** If the cohomology of `K` vanishes in degrees below `e` and `L` is
represented by a K-injective complex `I` concentrated in degrees `≤ d`, then the cohomology of
`RSheafHom(K, L)` vanishes in degrees above `d - e`. -/
public theorem isLE_derivedSheafHom
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (e d : ℤ) (hK : K.IsGE e)
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective] [CochainComplex.IsStrictlyLE I d] (eI : DerivedCategory.Q.obj I ≅ L) :
    (((derivedSheafHomBifunctor X).obj (op K)).obj L).IsLE (d - e) := by
  have := hK
  obtain ⟨P, hP, ⟨eP⟩⟩ := K.exists_iso_Q_obj_of_isGE e
  have := hP
  have hmodel :
      (DerivedCategory.Q.obj (sheafHomComplex X P I).obj).IsLE (d - e) := by
    have := isStrictlyLE_sheafHomComplex X P I e d
    infer_instance
  obtain ⟨iso⟩ := nonempty_iso_derivedSheafHom X eP eI
  exact DerivedCategory.TStructure.t.isLE_of_iso iso (d - e)

/-- **The derived internal Hom of a cohomologically bounded-above object into a
cohomologically bounded-below object is cohomologically bounded below.** No coherence,
finiteness or Noetherian hypothesis enters. -/
public theorem isBoundedBelow_derivedSheafHom
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : DerivedCategoryB.IsBoundedAbove K) (hL : DerivedCategoryB.IsBoundedBelow L) :
    DerivedCategoryB.IsBoundedBelow (((derivedSheafHomBifunctor X).obj (op K)).obj L) := by
  obtain ⟨d, hd⟩ := hK
  obtain ⟨b, hb⟩ := hL
  have hK' : K.IsLE (d + 1) := (DerivedCategory.isLE_iff K (d + 1)).mpr fun i hi =>
    hd i (by omega)
  have hL' : L.IsGE b := (DerivedCategory.isGE_iff L b).mpr hb
  exact ⟨b - (d + 1), fun i hi =>
    (DerivedCategory.isGE_iff _ (b - (d + 1))).1
      (isGE_derivedSheafHom X K L (d + 1) b hK' hL') i hi⟩

end AlgebraicGeometry.RingedSite

end
