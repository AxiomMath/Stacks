module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SitePointStalkAdditive
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseAcyclic
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisSplittingMap
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleShriekForgetStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleStalkConservative

/-!
# Part (1) of Stacks 08GV from the stalk degeneracies of an elementary distinguished square

Let `(U ⊆ X, j_V : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a
scheme `S`, let `P = U ×_X V` and let `F` be a sheaf of `𝒪_X`-modules.  The Mayer–Vietoris short
complex

`0 ⟶ j_{P!}F|_P ⟶ j_{U!}F|_U ⊕ j_{V!}F|_V ⟶ F ⟶ 0`

is a complex by `AlgebraicGeometry.Space.zero_edsShriekMayerVietoris`.  This file assembles its
short exactness — part (1) of Stacks 08GV — out of five statements about its stalks, which are
taken here as hypotheses:

* at a geometric point lying in `U`, the comparison out of the intersection and the counit of
  the extension by zero from `U` are invertible on stalks;
* at a geometric point not lying in `U`, the extensions by zero from `P` and from `U` have
  vanishing stalk and the counit of the extension by zero along `j_V` is invertible on stalks.

The assembly is complete: nothing beyond those five statements is used, and the two cases are
the two splitting criteria of
`StacksFrontier.Algebra.Homology.MayerVietorisSplitting`, applied to the stalk functor through
`CategoryTheory.ShortComplex.shortExact_map_of_isIso` and
`CategoryTheory.ShortComplex.shortExact_map_of_isZero`.  Monomorphy, epimorphy and exactness are
then detected on the conservative family of geometric points by
`AlgebraicGeometry.Space.mono_of_mono_geometricModuleStalk`,
`AlgebraicGeometry.Space.epi_of_epi_geometricModuleStalk` and
`Stacks.shortComplex_exact_of_forall_exact_map_sheafModuleFiber`.

## Main results

* `AlgebraicGeometry.Space.shortExact_edsShriekMayerVietoris_of_stalks`: the Mayer–Vietoris
  short complex is short exact as soon as the five stalk statements hold.

## Implementation notes

The hypotheses are stated for arbitrary extension-by-zero data `adjU`, `adjV`, `adjP`, as the
rest of this development does, and the proof uses nothing about them.  The five stalk
statements themselves are *not* proved here; they are where the geometry of the square enters,
through Equation 08GU and the lift counts of the square.

The case split on the geometric point is done once, in a single fact `key` about the image short
complex under the stalk functor, from which the three goals (exactness, monomorphy, epimorphy)
are read off.  The statement of `key` goes through `CategoryTheory.Functor.mapShortComplex`.

## References

* [Stacks Project, Tag 08GV](https://stacks.math.columbia.edu/tag/08GV)
* [Stacks Project, Tag 08GU](https://stacks.math.columbia.edu/tag/08GU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
  [HasSheafify (smallEtaleRingedSite B S hS W.1 W.2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS W.1 W.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {shriekU : Modules.{u, u} B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  {shriekV : Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  {shriekP : Modules.{u, u} B S hS (edsInter B S hS hsq).1 (edsInter B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  (adjU : shriekU ⊣ etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
    (isEtale_edsOpenHom B S hS hsq))
  (adjV : shriekV ⊣ etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq))
  (adjP : shriekP ⊣ etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
    (isEtale_edsInterHom B S hS hsq))

/-- The stalk functor at a geometric point on sheaves of modules over the structure sheaf of the
ambient algebraic space of an elementary distinguished square. -/
abbrev edsModuleStalk (x : GeometricPoint B S hS W.1) :=
  geometricModuleStalkFunctor B S hS W.1 W.2 (etaleRingSheaf B S hS W) x

/-- **Part (1) of Stacks 08GV from the stalk degeneracies.**  The Mayer–Vietoris short complex
of an elementary distinguished square is short exact as soon as, at every geometric point of the
ambient algebraic space, the comparison out of the intersection and the counit from the open
subspace are invertible on stalks where the point lies in the open subspace, and the two
extensions by zero from the intersection and from the open subspace have vanishing stalk and the
counit along the étale morphism is invertible on stalks where it does not. -/
theorem shortExact_edsShriekMayerVietoris_of_stalks
    (F : Modules.{u, u} B S hS W.1 W.2)
    (hbU : ∀ x : GeometricPoint B S hS W.1,
      x.image ∈ Set.range (pointsMap B S hS Uo.toFunctor Uo.ι) →
      IsIso ((edsModuleStalk B S hS x).map
        ((edsShriekEtaleComparison B S hS hsq adjV adjP).app F)))
    (hgU : ∀ x : GeometricPoint B S hS W.1,
      x.image ∈ Set.range (pointsMap B S hS Uo.toFunctor Uo.ι) →
      IsIso ((edsModuleStalk B S hS x).map (adjU.counit.app F)))
    (hPzero : ∀ x : GeometricPoint B S hS W.1,
      x.image ∉ Set.range (pointsMap B S hS Uo.toFunctor Uo.ι) →
      IsZero ((edsModuleStalk B S hS x).obj
        (shriekP.obj ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
          (isEtale_edsInterHom B S hS hsq)).obj F))))
    (hUzero : ∀ x : GeometricPoint B S hS W.1,
      x.image ∉ Set.range (pointsMap B S hS Uo.toFunctor Uo.ι) →
      IsZero ((edsModuleStalk B S hS x).obj
        (shriekU.obj ((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
          (isEtale_edsOpenHom B S hS hsq)).obj F))))
    (hdV : ∀ x : GeometricPoint B S hS W.1,
      x.image ∉ Set.range (pointsMap B S hS Uo.toFunctor Uo.ι) →
      IsIso ((edsModuleStalk B S hS x).map (adjV.counit.app F))) :
    (ShortComplex.mayerVietoris
      ((edsShriekOpenComparison B S hS hsq adjU adjP).app F)
      ((edsShriekEtaleComparison B S hS hsq adjV adjP).app F)
      (adjU.counit.app F) (adjV.counit.app F)
      (zero_edsShriekMayerVietoris B S hS hsq adjU adjV adjP F)).ShortExact := by
  classical
  have key : ∀ x : GeometricPoint B S hS W.1, ((edsModuleStalk B S hS x).mapShortComplex.obj
      (ShortComplex.mayerVietoris
      ((edsShriekOpenComparison B S hS hsq adjU adjP).app F)
      ((edsShriekEtaleComparison B S hS hsq adjV adjP).app F)
      (adjU.counit.app F) (adjV.counit.app F)
      (zero_edsShriekMayerVietoris B S hS hsq adjU adjV adjP F))).ShortExact := by
    intro x
    by_cases hx : x.image ∈ Set.range (pointsMap B S hS Uo.toFunctor Uo.ι)
    · exact ShortComplex.shortExact_map_of_isIso _ _ _ _ _ _ (hbU x hx) (hgU x hx)
    · exact ShortComplex.shortExact_map_of_isZero _ _ _ _ _ _ (hPzero x hx) (hUzero x hx)
        (hdV x hx)
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · refine Stacks.shortComplex_exact_of_forall_exact_map_sheafModuleFiber
      (etaleRingSheaf B S hS W)
      (isConservativeFamilyOfPoints_etaleSitePoint B S hS W.1 W.2) ?_
    rintro ⟨Φ, hΦ⟩
    obtain ⟨x, rfl⟩ := (ObjectProperty.ofObj_iff _ Φ).1 hΦ
    exact (key x).exact
  · exact mono_of_mono_geometricModuleStalk B S hS W.1 W.2 (etaleRingSheaf B S hS W) _
      fun x => (key x).mono_f
  · exact epi_of_epi_geometricModuleStalk B S hS W.1 W.2 (etaleRingSheaf B S hS W) _
      fun x => (key x).epi_g

end AlgebraicGeometry.Space

end
