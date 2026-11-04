module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EssentiallySmallDerivedInternalHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplexBoundedBelow
public import StacksFrontier.Algebra.Homology.Resolution.InjectiveResolution

/-!
# The derived internal Hom on an essentially small site is bounded below

On an essentially `u`-small ringed site, if the cohomology of `K` vanishes above degree `d` and
that of `L` below degree `b`, the cohomology of the derived internal Hom `RSheafHom(K, L)` of
`AlgebraicGeometry.RingedSite.derivedSheafHomSmallBifunctor` vanishes below degree `b - d`.

## Main results

* `AlgebraicGeometry.RingedSite.isStrictlyGE_sheafHomComplexSmall`: the internal Hom complex
  at the module universe of the site out of a complex concentrated in degrees `≤ d` into one
  concentrated in degrees `≥ b` is concentrated in degrees `≥ b - d`.
* `AlgebraicGeometry.RingedSite.isGE_derivedSheafHomSmall`: the same bound for the derived
  internal Hom.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe c u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{c, u, u}) [EssentiallySmall.{u} X.C]

/-- If `K` is concentrated in degrees `≤ d` and `M` in degrees `≥ b`, then the internal Hom
complex `AlgebraicGeometry.RingedSite.sheafHomComplexSmall X K M` is concentrated in degrees
`≥ b - d`. -/
theorem isStrictlyGE_sheafHomComplexSmall
    (K M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (d b : ℤ) [CochainComplex.IsStrictlyLE K d] [CochainComplex.IsStrictlyGE M b] :
    CochainComplex.IsStrictlyGE (sheafHomComplexSmall X K M) (b - d) := by
  have hbig := isStrictlyGE_sheafHomComplex X K M d b
  rw [CochainComplex.isStrictlyGE_iff] at hbig ⊢
  intro n hn
  rw [IsZero.iff_id_eq_zero]
  exact (Stacks.SheafOfModules.moduleULiftFullyFaithful.{max c u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map_injective
    (((hbig n hn).of_iso ((HomologicalComplex.eval _ _ n).mapIso
      (sheafHomComplexSmallIso X K M))).eq_of_src _ _)

variable [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{u + 1} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- On an essentially small ringed site, if the cohomology of `K` vanishes in degrees above `d`
and that of `L` in degrees below `b`, then the cohomology of `RSheafHom(K, L)` vanishes in degrees
below `b - d`. -/
theorem isGE_derivedSheafHomSmall
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (d b : ℤ) [K.IsLE d] [L.IsGE b] :
    (((derivedSheafHomSmallBifunctor X).obj (op K)).obj L).IsGE (b - d) := by
  obtain ⟨P, hP, ⟨eP⟩⟩ := K.exists_iso_Q_obj_of_isLE d
  obtain ⟨C, hC, ⟨eC⟩⟩ := L.exists_iso_Q_obj_of_isGE b
  obtain ⟨J, -, hJ⟩ := CochainComplex.exists_injectiveResolution_isStrictlyGE b C
  have : QuasiIso J.ι := J.quasiIso
  have hJinj : J.cocomplex.IsKInjective := CochainComplex.isKInjective_of_injective J.cocomplex b
  have := isStrictlyGE_sheafHomComplexSmall X P J.cocomplex d b
  let e : ((derivedSheafHomSmallBifunctor X).obj (op K)).obj L ≅
      DerivedCategory.Q.obj (sheafHomComplexSmall X P J.cocomplex) :=
    ((derivedSheafHomSmallBifunctor X).mapIso eP.symm.op).app L ≪≫
      ((derivedSheafHomSmallBifunctor X).obj (op (DerivedCategory.Q.obj P))).mapIso
        (eC ≪≫ asIso (DerivedCategory.Q.map J.ι)) ≪≫
      derivedSheafHomSmallResolutionComparison X P J.cocomplex ≪≫
      (asIso (DerivedCategory.Q.map
        (homMapSmall X (𝟙 P) ((kInjectiveAugmentationSmall X).app J.cocomplex)))).symm
  exact DerivedCategory.TStructure.t.isGE_of_iso e.symm (b - d)

end AlgebraicGeometry.RingedSite

end
