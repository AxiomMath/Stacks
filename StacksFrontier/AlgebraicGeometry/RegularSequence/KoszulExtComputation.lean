module

public import StacksFrontier.Algebra.Homology.HomologyOfZeroDifferentials
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulHomComplexVanishing
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulStrictPerfection
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomComplexOfAStrictlyPerfectComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.StrictlyPerfectHomKFlat

/-!
# The Ext sheaves of the quotient by a Koszul-regular ideal

Let `X` be a topological space, `O♯` a sheaf of commutative rings on it, `φ : (O♯)ʳ ⟶ O♯` a
morphism of sheaves of modules whose Koszul complex resolves the quotient `O_X = O♯/I` by the
ideal sheaf `I` it generates. This file computes the Ext sheaves of `O_X` over `O♯`:

`Ext^n_{O♯}(O_X, O_X) ≅ SheafHom_{O♯}(⋀ⁿ((O♯)ʳ), O_X)`.

Three facts combine. The Koszul complex, read as a cochain complex, is a strictly perfect
resolution of `O_X`, so the Ext sheaves are the cohomology sheaves of the naive internal Hom
complex out of it. That Hom complex has vanishing differential, so its cohomology sheaves are
its terms. And a term of the internal Hom complex into a complex concentrated in degree zero has
exactly one nonvanishing component, the one evaluating on the source in the matching degree.

## Main definitions

* `Stacks.Limits.isIso_fan_proj_of_isZero`: the projection of a product onto a factor is an
  isomorphism when every other factor is a zero object.
* `AlgebraicGeometry.RingedSite.homDegreeIsoSingle`: the degree-`n` term of the internal Hom
  complex into a complex concentrated in degree zero is `SheafHom(E^{-n}, N)`.
* `Stacks.RegularSequence.KoszulChainData.extIsoInternalHom`: **the Ext sheaves of `O♯/I` are
  the internal Hom sheaves out of the terms of the Koszul complex.**
* `Stacks.RegularSequence.KoszulChainData.extIsoInternalHomExteriorPower`: the same with the
  terms of the Koszul complex named as exterior powers.

## Implementation notes

The degree-`n` term of the internal Hom complex is a *product* over `q : ℤ` of the sheaves
`SheafHom(E^{-q}, F^{n-q})`, by `AlgebraicGeometry.RingedSite.homDegreeIsLimit`, which holds with
no hypothesis on either complex. For `F` concentrated in degree zero all factors but `q = n`
vanish, and a product of a family with one nonvanishing member is that member; the inverse of the
projection is written down from the universal property with `Function.update`, which avoids the
degree transport an `if`-expression would carry.

The Koszul complex is `ℤ`-indexed and the Hom complex is cohomologically indexed, so the term of
the resolution appearing in degree `n` is the Koszul term in degree `-(-n)`; that double negation
is the one transport in the main definition. The variant naming the Koszul terms as exterior
powers carries a second, the identification `chain.X n = ⋀ⁿF` which is part of the Koszul data.

## References

* [Stacks Project, Tag 08DM](https://stacks.math.columbia.edu/tag/08DM)
* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace
open AlgebraicGeometry HomologicalComplex

universe v u

namespace Stacks.Limits

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- **The projection of a product onto a factor is an isomorphism when every other factor is a
zero object.** The inverse is the morphism into the product whose component at the chosen index
is the identity and whose other components are zero. -/
theorem isIso_fan_proj_of_isZero {β : Type*} {f : β → C} {c : Fan f}
    (hc : IsLimit c) (b : β) (hz : ∀ b' : β, b' ≠ b → IsZero (f b')) :
    IsIso (c.proj b) := by
  classical
  refine ⟨Fan.IsLimit.lift hc
    (Function.update (fun b' : β => (0 : f b ⟶ f b')) b (𝟙 (f b))), ?_, ?_⟩
  · refine Fan.IsLimit.hom_ext hc _ _ fun b' => ?_
    rcases eq_or_ne b' b with rfl | hb'
    · rw [Category.assoc, Fan.IsLimit.fac hc, Function.update_self, Category.comp_id,
        Category.id_comp]
    · exact (hz b' hb').eq_of_tgt _ _
  · rw [Fan.IsLimit.fac hc, Function.update_self]

end Stacks.Limits

namespace AlgebraicGeometry.RingedSite

variable (Y : RingedSite.{u, u, u}) [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The only nonvanishing component of a term of the internal Hom complex into a complex
concentrated in degree zero** is the one evaluating on the source in the matching degree. -/
theorem isIso_homDegreeProjection_single
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (n : ℤ) :
    IsIso (homDegreeProjection Y E
      ((single (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (ComplexShape.up ℤ) 0).obj N) n n) := by
  have hz : ∀ q : ℤ, q ≠ n → IsZero (internalHomSheaf Y (E.X (-q))
      (((single (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (ComplexShape.up ℤ) 0).obj N).X (n - q))) := by
    intro q hq
    exact Stacks.SheafOfModules.internalHomSheaf_isZero_of_isZero_target Y
      (isZero_single_obj_X (ComplexShape.up ℤ) 0 N (n - q) (by omega))
  exact Stacks.Limits.isIso_fan_proj_of_isZero (homDegreeIsLimit Y E _ n) n hz

/-- **The degree-`n` term of the internal Hom complex into a complex concentrated in degree zero
is `SheafHom(E^{-n}, N)`.** -/
noncomputable def homDegreeIsoSingle
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (n : ℤ) :
    (sheafHomComplex Y E
        ((single (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          (ComplexShape.up ℤ) 0).obj N)).obj.X n ≅
      internalHomSheaf Y (E.X (-n)) N :=
  have := isIso_homDegreeProjection_single Y E N n
  asIso (homDegreeProjection Y E _ n n) ≪≫
    eqToIso (congrArg (internalHomSheaf Y (E.X (-n))) (by rw [sub_self]; rfl))

end AlgebraicGeometry.RingedSite

namespace Stacks.RegularSequence.KoszulChainData

open Stacks.SheafOfModules Stacks.ChainComplex

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {r : ℕ}
  {A : SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X)
    (koszulFreeSheaf Rc r)}
  {φ : koszulFreeSheaf Rc r ⟶
    SheafOfModules.unit (toRingCat (Opens.grothendieckTopology ↥X) Rc)}

/-- **The Ext sheaves of `O♯/I` are the internal Hom sheaves out of the terms of the Koszul
complex.** For `φ` whose Koszul complex resolves the quotient, and for every `n`,

`Ext^n_{O♯}(O♯/I, O♯/I) ≅ SheafHom_{O♯}(K_n, O♯/I)`,

where `K_n` is the degree-`n` term of the Koszul complex. The Koszul complex is a strictly
perfect resolution, the Hom complex out of it into the quotient has vanishing differential, and
a term of that Hom complex has a single nonvanishing component. -/
noncomputable def extIsoInternalHom (K : KoszulChainData.{u, u, u} A φ)
    [QuasiIso K.augmentation] (n : ℤ) :
    derivedSheafExt Rc
        (DerivedCategory.Q.obj
          ((single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).obj
            (quotient Rc (φ := φ))))
        (DerivedCategory.Q.obj
          ((single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).obj
            (quotient Rc (φ := φ)))) n ≅
      RingedSite.internalHomSheaf (ringedSite Rc) (K.chain.X n) (quotient Rc (φ := φ)) :=
  derivedSheafExtIsoHomologyCochain Rc K _ n ≪≫
    Stacks.CochainComplex.intHomologyIsoX _ (sheafHomComplex_d_eq_zero K) n ≪≫
    RingedSite.homDegreeIsoSingle (ringedSite Rc) (cochain Rc K) (quotient Rc (φ := φ)) n ≪≫
    eqToIso (congrArg (fun M => RingedSite.internalHomSheaf (ringedSite Rc) M
      (quotient Rc (φ := φ))) (congrArg K.chain.X (neg_neg n)))

/-- **The Ext sheaves of `O♯/I` are the internal Hom sheaves out of the exterior powers of
`(O♯)ʳ`:**

`Ext^m_{O♯}(O♯/I, O♯/I) ≅ SheafHom_{O♯}(⋀ᵐ((O♯)ʳ), O♯/I)`

for every natural number `m`. This is
`Stacks.RegularSequence.KoszulChainData.extIsoInternalHom` with the term of the Koszul complex
named by the identification which is part of the Koszul data. -/
noncomputable def extIsoInternalHomExteriorPower (K : KoszulChainData.{u, u, u} A φ)
    [QuasiIso K.augmentation] (m : ℕ) :
    derivedSheafExt Rc
        (DerivedCategory.Q.obj
          ((single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).obj
            (quotient Rc (φ := φ))))
        (DerivedCategory.Q.obj
          ((single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).obj
            (quotient Rc (φ := φ)))) ((m : ℕ) : ℤ) ≅
      RingedSite.internalHomSheaf (ringedSite Rc) (A.exteriorPower m) (quotient Rc (φ := φ)) :=
  extIsoInternalHom Rc K ((m : ℕ) : ℤ) ≪≫
    eqToIso (congrArg (fun M => RingedSite.internalHomSheaf (ringedSite Rc) M
      (quotient Rc (φ := φ))) (K.chain_X ((m : ℕ) : ℤ)))

end Stacks.RegularSequence.KoszulChainData

end
