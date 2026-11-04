module

public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportInternalHomBridge
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplexSingleSourceDifferential

/-!
# The internal Hom complex out of `i_* 𝒪_Z`, and the trace

Let `i : Z ⟶ X` be a closed quotient morphism of ringed spaces and `I` a cochain complex of
`𝒪_X`-modules.  The internal Hom identification of [Stacks, Tag 0A75] gives, degreewise,
`i_* ℰom(𝒪_Z, I^n) ≅ ℰom_{𝒪_X}(i_* 𝒪_Z, I^n)`, and the right-hand side is the degree-`n` term of
the internal Hom complex `SheafHom^•_{𝒪_X}((i_* 𝒪_Z)[0], I)` of [Stacks, Tag 0A8Z], the source
being concentrated in degree zero.  Those identifications assemble into an isomorphism of
complexes

`i_* ℰom^•(𝒪_Z, I) ≅ SheafHom^•_{𝒪_X}((i_* 𝒪_Z)[0], I)`,

and under it the counit of [Stacks, Tag 0A75] — evaluation of a local homomorphism at the
section `1` — is precomposition with a map `𝒪_X[0] ⟶ (i_* 𝒪_Z)[0]` carrying `1` to `1`, followed
by evaluation at the unit section.

This is the complex-level input to the trace description of the duality isomorphism of an
effective Cartier divisor: it is what lets the trace of [Stacks, Tag 0A76] be recognised inside
the derived internal Hom *bifunctor*, where the comparison of triangles of [Stacks, Tag 08I0]
lives.

## Main definitions

* `…exactSupportInternalHomIso`: the degreewise identification
  `i_* ℰom(𝒪_Z, G) ≅ ℰom_{𝒪_X}(i_* 𝒪_Z, G)`, the internal Hom identification of
  [Stacks, Tag 0A75] read in the internal Hom sheaf of [Stacks, Tag 03EM].
* `…exactSupportHomComplexIso`: the resulting isomorphism of complexes.

## Main results

* `…exactSupportInternalHomIso_naturality`: the degreewise identification is natural, which is
  what makes it a morphism of complexes.
* `…exactSupportHomComplexIso_comp_evaluation`: **the trace, degreewise.** The isomorphism of
  complexes, followed by precomposition with a map `𝒪_X[0] ⟶ (i_* 𝒪_Z)[0]` sending `1` to `1`
  and then by evaluation at the unit section, is the counit of [Stacks, Tag 0A75] applied
  degreewise.

## Implementation notes

The differential of the internal Hom complex out of a complex concentrated in degree zero is
postcomposition with the differential of the target, with no sign: the Leibniz rule's other
term is the evaluation on the differential of the source, which vanishes.  That is what
`AlgebraicGeometry.RingedSite.applyHomSectionOver_differential` together with
`AlgebraicGeometry.RingedSite.applyHomSectionOver_eq_zero_of_isZero` supplies, and it is why the
comparison is a morphism of complexes with no correction.

Both the morphism-of-complexes property and the trace identity are checked on sections, through
`AlgebraicGeometry.RingedSite.homSection_ext`: a section of the internal Hom complex is
determined by its evaluations, and in every bidegree but `(0, n)` the source of the evaluation
is a zero object.

## References

* [Stacks Project, Tag 0A75](https://stacks.math.columbia.edu/tag/0A75)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u})

/-- `(i_* 𝒪_Z)[0]`, the pushed-forward structure sheaf placed in degree zero. -/
abbrev pushforwardStructureSingleComplex :
    CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ :=
  AlgebraicGeometry.RingedSite.sgl (ringedSiteX S) (pushforwardStructureModule S)

/-- **`i_* ℰom(𝒪_Z, G) ≅ ℰom_{𝒪_X}(i_* 𝒪_Z, G)`**: the internal Hom identification of
[Stacks, Tag 0A75], read in the internal Hom sheaf of [Stacks, Tag 03EM]. -/
def exactSupportInternalHomIso (G : SheafOfModules.{u} (structureSheafRing S.X)) :
    (S.sheafHomExactSupport ⋙ modulePushforward S.i).obj G ≅
      AlgebraicGeometry.RingedSite.internalHomSheaf (ringedSiteX S)
        (pushforwardStructureModule S) G :=
  S.modulePushforwardSheafHomExactSupportIsoHomSheaf.app G ≪≫ internalHomComparisonIso S G

/-- The degreewise identification is the internal Hom identification of [Stacks, Tag 0A75]
followed by the comparison of the two spellings. -/
theorem exactSupportInternalHomIso_hom (G : SheafOfModules.{u} (structureSheafRing S.X)) :
    (exactSupportInternalHomIso S G).hom =
      S.modulePushforwardSheafHomExactSupportIsoHomSheaf.hom.app G ≫
        internalHomComparison S G :=
  rfl

/-- The degreewise identification is natural in the module: both sides act on a morphism of the
target by postcomposition. -/
theorem exactSupportInternalHomIso_naturality
    {G H : SheafOfModules.{u} (structureSheafRing S.X)} (g : G ⟶ H) :
    (S.sheafHomExactSupport ⋙ modulePushforward S.i).map g ≫
        (exactSupportInternalHomIso S H).hom =
      (exactSupportInternalHomIso S G).hom ≫
        AlgebraicGeometry.RingedSite.internalHomPost (ringedSiteX S) g := by
  refine Eq.trans (Category.assoc _ _ _).symm (Eq.trans (congrArg
    (fun t => t ≫ internalHomComparison S H)
    (S.modulePushforwardSheafHomExactSupportIsoHomSheaf.hom.naturality g)) ?_)
  refine Eq.trans (Category.assoc _ _ _) (Eq.trans (congrArg
    (fun t => S.modulePushforwardSheafHomExactSupportIsoHomSheaf.hom.app G ≫ t)
    (internalHomComparison_naturality S g)) ?_)
  exact (Category.assoc _ _ _).symm

variable (I : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ)

/-- The degree-`n` component of the comparison of `i_* ℰom^•(𝒪_Z, I)` with the internal Hom
complex out of `(i_* 𝒪_Z)[0]`. -/
def exactSupportHomComplexComponentIso (n : ℤ) :
    (((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).X n ≅
      (AlgebraicGeometry.RingedSite.sheafHomComplex (ringedSiteX S)
        (pushforwardStructureSingleComplex S) I).obj.X n :=
  exactSupportInternalHomIso S (I.X n) ≪≫
    (AlgebraicGeometry.RingedSite.homComponentIsoOfEq (ringedSiteX S) 0 n n (zero_add n)
      (AlgebraicGeometry.RingedSite.isZero_sgl_X (ringedSiteX S)
        (pushforwardStructureModule S))).symm

/-- The degree-`n` component of the comparison, evaluated on a local section of
`(i_* 𝒪_Z)[0]` in degree zero: the local homomorphism the identification of [Stacks, Tag 0A75]
attaches to the section. -/
theorem applyHomSectionOver_exactSupportHomComplexComponentIso (n : ℤ) (U V : Opens S.X)
    (a : V ⟶ U)
    (s : ((((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).X n).val.obj
        (op U))
    (x : ((pushforwardStructureSingleComplex S).X 0).val.obj (op V)) :
    AlgebraicGeometry.RingedSite.applyHomSectionOver (ringedSiteX S)
        (AlgebraicGeometry.RingedSite.sheafHomComplex (ringedSiteX S)
          (pushforwardStructureSingleComplex S) I) U V a n 0 n (zero_add n)
        ((exactSupportHomComplexComponentIso S I n).hom.val.app (op U) s) x =
      PresheafOfModules.Hom.app
        ((exactSupportInternalHomIso S (I.X n)).hom.val.app (op U) s) (op (Over.mk a)) x :=
  AlgebraicGeometry.RingedSite.applyHomSectionOver_homComponentIsoOfEq_inv (ringedSiteX S)
    0 n n (zero_add n)
    (AlgebraicGeometry.RingedSite.isZero_sgl_X (ringedSiteX S) (pushforwardStructureModule S))
    U V a _ x

/-- **`i_* ℰom^•(𝒪_Z, I) ≅ SheafHom^•_{𝒪_X}((i_* 𝒪_Z)[0], I)`.**  The degreewise internal Hom
identification of [Stacks, Tag 0A75] is a morphism of complexes: the differential of the
internal Hom complex out of a source concentrated in degree zero is postcomposition with the
differential of the target. -/
def exactSupportHomComplexIso :
    ((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≅
      (AlgebraicGeometry.RingedSite.sheafHomComplex (ringedSiteX S)
        (pushforwardStructureSingleComplex S) I).obj :=
  HomologicalComplex.Hom.isoOfComponents (exactSupportHomComplexComponentIso S I) (by
    have hsplit : ∀ {M N P : SheafOfModules.{u} (structureSheafRing S.X)} (f : M ⟶ N) (g : N ⟶ P)
        (W : (Opens S.X)ᵒᵖ) (t : (M.val.obj W : Type u)),
        (ModuleCat.Hom.hom ((f ≫ g).val.app W)) t =
          (ModuleCat.Hom.hom (g.val.app W)) ((ModuleCat.Hom.hom (f.val.app W)) t) :=
      fun _ _ _ _ => rfl
    intro n j hnj
    obtain rfl : n + 1 = j := hnj
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ?_)
    obtain ⟨U⟩ := U
    refine ModuleCat.hom_ext (LinearMap.ext fun s => ?_)
    refine AlgebraicGeometry.RingedSite.homSection_ext (ringedSiteX S)
      (AlgebraicGeometry.RingedSite.sheafHomComplex (ringedSiteX S)
        (pushforwardStructureSingleComplex S) I) U (n + 1) ?_
    intro p q hpq V a x
    by_cases hp : p = 0
    · subst hp
      obtain rfl : q = n + 1 := by omega
      rw [hsplit, hsplit]
      refine Eq.trans (AlgebraicGeometry.RingedSite.applyHomSectionOver_differential_sgl
        (ringedSiteX S) (pushforwardStructureModule S) I U V a n n (n + 1) (zero_add n) rfl
        ((exactSupportHomComplexComponentIso S I n).hom.val.app (op U) s) x) ?_
      refine Eq.trans (congrArg
        (fun z : ((I.X n).val.obj (op V) : Type u) =>
          (ModuleCat.Hom.hom ((I.d n (n + 1)).val.app (op V))) z)
        (applyHomSectionOver_exactSupportHomComplexComponentIso S I n U V a s x)) ?_
      refine Eq.trans ?_ (applyHomSectionOver_exactSupportHomComplexComponentIso S I (n + 1)
        U V a _ x).symm
      refine Eq.trans ?_ (congrArg
        (fun t : (S.sheafHomExactSupport ⋙ modulePushforward S.i).obj (I.X n) ⟶
            AlgebraicGeometry.RingedSite.internalHomSheaf (ringedSiteX S)
              (pushforwardStructureModule S) (I.X (n + 1)) =>
          PresheafOfModules.Hom.app ((SheafOfModules.Hom.val t).app (op U) s)
            (op (Over.mk a)) x)
        (exactSupportInternalHomIso_naturality S (I.d n (n + 1)))).symm
      exact (AlgebraicGeometry.RingedSite.internalHomPost_val_app_apply (ringedSiteX S)
        (I.d n (n + 1)) U V a _ x).symm
    · exact Eq.trans
        (AlgebraicGeometry.RingedSite.applyHomSectionOver_eq_zero_of_isZero (ringedSiteX S)
          U V a (n + 1) p q hpq
          (AlgebraicGeometry.RingedSite.isZero_sgl_X (ringedSiteX S)
            (pushforwardStructureModule S) p hp) _ x)
        (AlgebraicGeometry.RingedSite.applyHomSectionOver_eq_zero_of_isZero (ringedSiteX S)
          U V a (n + 1) p q hpq
          (AlgebraicGeometry.RingedSite.isZero_sgl_X (ringedSiteX S)
            (pushforwardStructureModule S) p hp) _ x).symm)

/-- The degreewise components of the comparison of complexes. -/
theorem exactSupportHomComplexIso_hom_f (n : ℤ) :
    (exactSupportHomComplexIso S I).hom.f n = (exactSupportHomComplexComponentIso S I n).hom :=
  rfl

/-- **The trace, degreewise.**  The comparison of `i_* ℰom^•(𝒪_Z, I)` with the internal Hom
complex out of `(i_* 𝒪_Z)[0]`, followed by precomposition with a map
`w : 𝒪_X[0] ⟶ (i_* 𝒪_Z)[0]` carrying the unit section to the unit section and then by
evaluation at the unit section, is the counit of [Stacks, Tag 0A75] applied degreewise.

Both sides evaluate a local homomorphism out of `i_* 𝒪_Z` at the section `1`: on the left
because `w` carries `1` to `1` and evaluation at the unit section is what
`AlgebraicGeometry.RingedSite.structureSheafHomEvaluation` does, on the right because the counit
of [Stacks, Tag 0A75] is evaluation at `1` read through the internal Hom identification
(`…modulePushforwardSheafHomExactSupportAdjunction_counit_app`). -/
theorem exactSupportHomComplexIso_comp_evaluation
    (w : AlgebraicGeometry.RingedSite.structureSheafComplex (ringedSiteX S) ⟶
      pushforwardStructureSingleComplex S)
    (hw : ∀ U : Opens S.X, ((w.f 0).val.app (op U))
        (AlgebraicGeometry.RingedSite.structureSheafOne (ringedSiteX S) U) =
      (1 : (S.pushedRingSheaf.obj.obj (op U) : Type u))) :
    (exactSupportHomComplexIso S I).hom ≫
        AlgebraicGeometry.RingedSite.homMap (ringedSiteX S) w (𝟙 I) ≫
          AlgebraicGeometry.RingedSite.structureSheafHomEvaluation (ringedSiteX S) I =
      (Adjunction.mapHomologicalComplexAdjunction
        S.modulePushforwardSheafHomExactSupportAdjunction (ComplexShape.up ℤ)).counit.app I := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ?_)
  obtain ⟨U⟩ := U
  refine ModuleCat.hom_ext (LinearMap.ext fun s => ?_)
  refine Eq.trans
    (AlgebraicGeometry.RingedSite.structureSheafHomEvaluation_apply (ringedSiteX S) I n U _) ?_
  refine Eq.trans
    (AlgebraicGeometry.RingedSite.applyHomSection_homMap (ringedSiteX S) w (𝟙 I) U n 0 n
      (zero_add n) _ (AlgebraicGeometry.RingedSite.structureSheafOne (ringedSiteX S) U)) ?_
  refine Eq.trans (congrArg
    (fun y : ((pushforwardStructureSingleComplex S).X 0).val.obj (op U) =>
      AlgebraicGeometry.RingedSite.applyHomSection (ringedSiteX S)
        (AlgebraicGeometry.RingedSite.sheafHomComplex (ringedSiteX S)
          (pushforwardStructureSingleComplex S) I) U n 0 n (zero_add n)
        (((exactSupportHomComplexIso S I).hom.f n).val.app (op U) s) y)
    (hw U)) ?_
  exact Eq.trans
    (applyHomSectionOver_exactSupportHomComplexComponentIso S I n U U (𝟙 U) s
      (1 : (S.pushedRingSheaf.obj.obj (op U) : Type u)))
    (S.modulePushforwardSheafHomExactSupportAdjunction_counit_app (I.X n) U s).symm

end RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

end
