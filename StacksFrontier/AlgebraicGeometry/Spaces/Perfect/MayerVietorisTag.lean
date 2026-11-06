module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModuleExtensionByZeroExact
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisComparisonStalk

/-!
# Stacks 08GV, both clauses

Let `(U ⊆ X, j_V : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a
scheme `S` and let `P = U ×_X V` be its intersection.  Write `(-)|_Y` for restriction of modules
along an étale morphism `j_Y : Y ⟶ X` and `j_{Y!}` for its extension by zero, the left adjoint
`AlgebraicGeometry.Space.etaleModuleLowerShriek`, with counit `j_{Y!}(F|_Y) ⟶ F`, and let
`a : j_{P!}((-)|_P) ⟶ j_{U!}((-)|_U)` and `b : j_{P!}((-)|_P) ⟶ j_{V!}((-)|_V)` be the two
comparisons attached to the two factorizations of `j_P`.  Then:

1. for every sheaf of `𝒪_X`-modules `F` the sequence

   `0 ⟶ j_{P!}F|_P ⟶ j_{U!}F|_U ⊕ j_{V!}F|_V ⟶ F ⟶ 0`,

   with maps `(a, -b)` and the sum of the two counits, is short exact;
2. every object `E` of the unbounded derived category `D(𝒪_X)` sits in a distinguished triangle

   `j_{P!}E|_P ⟶ j_{U!}E|_U ⊕ j_{V!}E|_V ⟶ E ⟶ (j_{P!}E|_P)[1]`,

   whose first two maps are the derived transformations of `(a, -b)` and of the two counits.

## Main results

* `AlgebraicGeometry.Space.mayerVietoris_shortExact_and_mem_distTriang`: **Stacks 08GV**, both
  clauses, for the extensions by zero of
  `StacksFrontier/AlgebraicGeometry/Spaces/EtaleModuleExtensionByZero.lean`.
* `AlgebraicGeometry.Space.shortExact_edsShriekMayerVietoris`: clause 1 for an arbitrary choice
  of extension-by-zero data, which is the form its consumers inside this development use.

## Implementation notes

The tag is stated for the extensions by zero the library constructs,
`AlgebraicGeometry.Space.etaleModuleLowerShriek`, and their adjunctions
`AlgebraicGeometry.Space.etaleModuleLowerShriekAdjunction`; nothing about them is assumed.  In
particular their exactness, Stacks 03DJ, is not an instance argument of the statement but the
theorem `AlgebraicGeometry.Space.preservesFiniteLimits_etaleModuleLowerShriek` of
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleModuleExtensionByZeroExact.lean`, and the
sheafification hypotheses of the ambient site are discharged by
`AlgebraicGeometry.Space.smallEtaleRingedSite_hasSheafify_addCommGrpCat` and
`AlgebraicGeometry.Space.smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat`, which
restate for the projection of `AlgebraicGeometry.Space.smallEtaleRingedSite` what instance search
cannot see through it.

Clause 1 is proved at the geometric points: the three functors are evaluated on stalks, where
Equation 08GU turns an extension by zero into a direct sum over the lifts of the point and the
lift counts of the square make the sequence split, by one of the two criteria of
`StacksFrontier.Algebra.Homology.MayerVietorisSplitting`.  Clause 2 is then the source's own
deduction, `AlgebraicGeometry.Space.mem_distTriang_mayerVietoris`, fed with clause 1.

`AlgebraicGeometry.Space.shortExact_edsShriekMayerVietoris` is kept for an arbitrary choice of
extension-by-zero data because that is the form in which Stacks 08H9,
`AlgebraicGeometry.Space.mem_distTriang_mayerVietorisExt`, consumes it; it carries no tag.  The
two maps out of the intersection are, by contrast, *not* hypotheses even there but the
comparisons `AlgebraicGeometry.Space.edsShriekOpenComparison` and
`AlgebraicGeometry.Space.edsShriekEtaleComparison` of the square.  They cannot be left
arbitrary: with the counit from `U` invertible on the stalk at a point of `U`, exactness in the
middle there is *equivalent* to invertibility of the comparison towards `V`, and compatibility
with the counits does not pin that comparison down once the point has two or more lifts along
`j_V`.  Clause 1 is a statement about the maps of the square, which is what the source states.

## References

* [Stacks Project, Tag 08GV](https://stacks.math.columbia.edu/tag/08GV)
* [Stacks Project, Tag 08GU](https://stacks.math.columbia.edu/tag/08GU)
* [Stacks Project, Tag 03DJ](https://stacks.math.columbia.edu/tag/03DJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

section Sheafify

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Abelian presheaves on the small étale site of an algebraic space are sheafifiable, restated
for the Grothendieck topology projected out of
`AlgebraicGeometry.Space.smallEtaleRingedSite`, which instance search does not unfold.

The content is `AlgebraicGeometry.Space.SmallEtale.instHasSheafify`, exactly as
`AlgebraicGeometry.Space.smallEtaleRingedSite_hasWeakSheafify_over` restates the corresponding
statement for the slices. -/
theorem smallEtaleRingedSite_hasSheafify_addCommGrpCat (Z : AlgebraicSpaces B S hS) :
    HasSheafify (smallEtaleRingedSite B S hS Z.1 Z.2).J AddCommGrpCat.{u} := by
  show HasSheafify (SmallEtale.topology B S hS Z.1) AddCommGrpCat.{u}
  infer_instance

/-- On the small étale site of an algebraic space the local isomorphisms of abelian sheaves are
the locally bijective maps, restated for the Grothendieck topology projected out of
`AlgebraicGeometry.Space.smallEtaleRingedSite`, which instance search does not unfold. -/
theorem smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat (Z : AlgebraicSpaces B S hS) :
    (smallEtaleRingedSite B S hS Z.1 Z.2).J.WEqualsLocallyBijective AddCommGrpCat.{u} := by
  show (SmallEtale.topology B S hS Z.1).WEqualsLocallyBijective AddCommGrpCat.{u}
  infer_instance

end Sheafify

section General

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

/-- **The Mayer–Vietoris short exact sequence of an elementary distinguished square, for an
arbitrary choice of extension-by-zero data.**  For an elementary distinguished square
`(U ⊆ X, V ⟶ X)` with intersection `P = U ×_X V`, a left adjoint `j_{Y!}` of restriction of
modules along each of the three étale morphisms, and a sheaf of `𝒪_X`-modules `F`, the sequence

`0 ⟶ j_{P!}F|_P ⟶ j_{U!}F|_U ⊕ j_{V!}F|_V ⟶ F ⟶ 0`,

with maps the two comparisons out of the intersection and the sum of the two counits, is short
exact.

Deliberately untagged.  Stacks 08GV is
`AlgebraicGeometry.Space.mayerVietoris_shortExact_and_mem_distTriang`, which states it for the
extension by zero the library constructs; this is the shape in which Stacks 08H9 consumes
clause 1, and the two agree because the chosen adjunction is one of the choices quantified
over here. -/
theorem shortExact_edsShriekMayerVietoris (F : Modules.{u, u} B S hS W.1 W.2) :
    (ShortComplex.mayerVietoris
      ((edsShriekOpenComparison B S hS hsq adjU adjP).app F)
      ((edsShriekEtaleComparison B S hS hsq adjV adjP).app F)
      (adjU.counit.app F) (adjV.counit.app F)
      (zero_edsShriekMayerVietoris B S hS hsq adjU adjV adjP F)).ShortExact :=
  shortExact_edsShriekMayerVietoris_of_stalks B S hS hsq adjU adjV adjP F
    (fun x hx => isIso_edsModuleStalk_edsShriekEtaleComparison_of_mem B S hS hsq adjV adjP F x hx)
    (fun x hx => isIso_edsModuleStalk_edsOpen_counit_of_mem B S hS hsq adjU F x hx)
    (fun x hx => isZero_edsModuleStalk_edsInter_shriek_of_notMem B S hS hsq adjP F x hx)
    (fun x hx => isZero_edsModuleStalk_edsOpen_shriek_of_notMem B S hS hsq adjU F x hx)
    (fun x hx => isIso_edsModuleStalk_edsEtale_counit_of_notMem B S hS hsq adjV F x hx)

end General

section Tag

attribute [local instance] smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- **Stacks 08GV.**  Let `(U ⊆ X, j_V : V ⟶ X)` be an elementary distinguished square of
algebraic spaces over a scheme `S` and let `P = U ×_X V`.  Write `(-)|_Y` for restriction of
modules along an étale morphism `j_Y : Y ⟶ X` and `j_{Y!}` for its extension by zero,
`AlgebraicGeometry.Space.etaleModuleLowerShriek`, with counit `j_{Y!}(F|_Y) ⟶ F`, and let `a`
and `b` be the two comparisons out of the intersection attached to its two factorizations.
Then

1. for every sheaf of `𝒪_X`-modules `F` the sequence

   `0 ⟶ j_{P!}F|_P ⟶ j_{U!}F|_U ⊕ j_{V!}F|_V ⟶ F ⟶ 0`,

   with maps `(a, -b)` and the sum of the two counits, is short exact, and
2. every object `E` of the unbounded derived category `D(𝒪_X)` sits in a distinguished triangle

   `j_{P!}E|_P ⟶ j_{U!}E|_U ⊕ j_{V!}E|_V ⟶ E ⟶ (j_{P!}E|_P)[1]`,

   whose first two maps are the derived transformations of `(a, -b)` and of the two counits.

The exactness of the three extensions by zero, Stacks 03DJ, is the theorem
`AlgebraicGeometry.Space.preservesFiniteLimits_etaleModuleLowerShriek` together with
`AlgebraicGeometry.Space.etaleModuleLowerShriek_additive` and
`AlgebraicGeometry.Space.preservesFiniteColimits_etaleModuleLowerShriek`, which is what makes
their derived functors available; it is proved, not assumed. -/
@[stacks 08GV]
theorem mayerVietoris_shortExact_and_mem_distTriang :
    (∀ F : Modules.{u, u} B S hS W.1 W.2,
        (ShortComplex.mayerVietoris
          ((edsShriekOpenComparison B S hS hsq
              (etaleModuleLowerShriekAdjunction B S hS (edsOpenHom B S hS hsq)
                (isEtale_edsOpenHom B S hS hsq))
              (etaleModuleLowerShriekAdjunction B S hS (edsInterHom B S hS hsq)
                (isEtale_edsInterHom B S hS hsq))).app F)
          ((edsShriekEtaleComparison B S hS hsq
              (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
                (isEtale_edsEtaleHom B S hS hsq))
              (etaleModuleLowerShriekAdjunction B S hS (edsInterHom B S hS hsq)
                (isEtale_edsInterHom B S hS hsq))).app F)
          ((etaleModuleLowerShriekAdjunction B S hS (edsOpenHom B S hS hsq)
            (isEtale_edsOpenHom B S hS hsq)).counit.app F)
          ((etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
            (isEtale_edsEtaleHom B S hS hsq)).counit.app F)
          (zero_edsShriekMayerVietoris B S hS hsq
            (etaleModuleLowerShriekAdjunction B S hS (edsOpenHom B S hS hsq)
              (isEtale_edsOpenHom B S hS hsq))
            (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
              (isEtale_edsEtaleHom B S hS hsq))
            (etaleModuleLowerShriekAdjunction B S hS (edsInterHom B S hS hsq)
              (isEtale_edsInterHom B S hS hsq)) F)).ShortExact) ∧
      ∀ E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2),
        ∃ δ, Triangle.mk
            (biprod.lift
              ((NatTrans.mapDerivedCategory
                (edsShriekOpenComparison B S hS hsq
                  (etaleModuleLowerShriekAdjunction B S hS (edsOpenHom B S hS hsq)
                    (isEtale_edsOpenHom B S hS hsq))
                  (etaleModuleLowerShriekAdjunction B S hS (edsInterHom B S hS hsq)
                    (isEtale_edsInterHom B S hS hsq)))).app E)
              (-((NatTrans.mapDerivedCategory
                (edsShriekEtaleComparison B S hS hsq
                  (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
                    (isEtale_edsEtaleHom B S hS hsq))
                  (etaleModuleLowerShriekAdjunction B S hS (edsInterHom B S hS hsq)
                    (isEtale_edsInterHom B S hS hsq)))).app E)))
            (biprod.desc
                ((NatTrans.mapDerivedCategory
                  (etaleModuleLowerShriekAdjunction B S hS (edsOpenHom B S hS hsq)
                    (isEtale_edsOpenHom B S hS hsq)).counit).app E)
                ((NatTrans.mapDerivedCategory
                  (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
                    (isEtale_edsEtaleHom B S hS hsq)).counit).app E) ≫
              (Functor.mapDerivedCategoryIdIso
                (Modules.{u, u} B S hS W.1 W.2)).hom.app E) δ ∈
          distTriang (DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) :=
  by
  have h := fun F : Modules.{u, u} B S hS W.1 W.2 =>
    shortExact_edsShriekMayerVietoris B S hS hsq
      (etaleModuleLowerShriekAdjunction B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq))
      (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq))
      (etaleModuleLowerShriekAdjunction B S hS (edsInterHom B S hS hsq)
        (isEtale_edsInterHom B S hS hsq)) F
  exact ⟨h, fun E => mem_distTriang_mayerVietoris B S hS hsq
      (etaleModuleLowerShriekAdjunction B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq))
      (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq))
      (edsShriekOpenComparison B S hS hsq
        (etaleModuleLowerShriekAdjunction B S hS (edsOpenHom B S hS hsq)
          (isEtale_edsOpenHom B S hS hsq))
        (etaleModuleLowerShriekAdjunction B S hS (edsInterHom B S hS hsq)
          (isEtale_edsInterHom B S hS hsq)))
      (edsShriekEtaleComparison B S hS hsq
        (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
          (isEtale_edsEtaleHom B S hS hsq))
        (etaleModuleLowerShriekAdjunction B S hS (edsInterHom B S hS hsq)
          (isEtale_edsInterHom B S hS hsq)))
      (zero_edsShriekMayerVietoris B S hS hsq
        (etaleModuleLowerShriekAdjunction B S hS (edsOpenHom B S hS hsq)
          (isEtale_edsOpenHom B S hS hsq))
        (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
          (isEtale_edsEtaleHom B S hS hsq))
        (etaleModuleLowerShriekAdjunction B S hS (edsInterHom B S hS hsq)
          (isEtale_edsInterHom B S hS hsq))) h E⟩

end Tag

end AlgebraicGeometry.Space

end
