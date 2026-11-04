module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.CategoryTheory.Abelian.Injective.Extend
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietoris.DerivedCanonicalMapAndTriangle
public import StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietoris.ShortExactSectionsAndComparison
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# The canonical map of a square at a sheaf with acyclic corners

Let `E ⟶ Y`, `Z ⟶ X` be a commutative square in a site carrying a sheaf of rings, and let `M` be
a sheaf of modules. Stacks 0F16 attaches to every K-injective complex `I` the canonical map
`c : I(X) ⟶ C(β)[-1]`. When `I` resolves `M` and the sections functors over the four corners
of the square are computed on `M` itself — that is, when sections over each corner carry the
resolution `M ⟶ I` to a quasi-isomorphism — the map `c` is a quasi-isomorphism exactly when the
sections sequence

`0 ⟶ M(X) ⟶ M(Z) ⊞ M(Y) ⟶ M(E) ⟶ 0`

is short exact. This is the computation behind the proof of Stacks 0EWT: there the higher
cohomology of `𝒪^{perf}` vanishes on the four corners of each square to be tested, so the
condition of Stacks 0EWR reduces to a short exact sequence of sections. The converse direction,
used for the Mayer–Vietoris sequence of an open covering by two opens, recovers acyclicity of
`X` from that of the three other corners.

## Main results

* `Stacks.MayerVietoris.CanonicalMapOfComplexes.General.quasiIso_mappingCoconeMap`: a chain map
  inducing quasi-isomorphisms on the sections over the three corners `X₁, X₂, X₃` induces a
  quasi-isomorphism of the mapping cocones of Stacks 0F16.
* `quasiIso_cSquare_of_quasiIso` and `quasiIso_complexFunctor_map_of_quasiIso_cSquare`, both in
  the namespace `Stacks.MayerVietoris.CanonicalMapOfComplexes.General`: the two-out-of-three
  consequences of the naturality of the canonical map.
* `Stacks.MayerVietoris.CanonicalMapOfComplexes.quasiIso_cSquare_of_shortExact`: if the sections
  over the four corners carry the resolution `M ⟶ I` to quasi-isomorphisms and the sections
  sequence of `M` is short exact, the canonical map of `I` is a quasi-isomorphism.
* `Stacks.MayerVietoris.CanonicalMapOfComplexes.quasiIso_sections_map_of_quasiIso_cSquare`: if the
  canonical map of `I` is a quasi-isomorphism, the sections over `X₁, X₂, X₃` carry the resolution
  to quasi-isomorphisms and the sections sequence of `M` is short exact, then so do the sections
  over `X₄`.

## Implementation notes

Both statements are naturality of the canonical map in the complex, applied to the resolution
`M[0] ⟶ I`: the canonical map of the single complex `M[0]` is a quasi-isomorphism by
`Stacks.Cohomology.MayerVietoris.quasiIso_cSquare_of_sectionsShortExact`, since its sections
sequence is short exact in degree zero and zero elsewhere, and the induced map of mapping cocones
is a quasi-isomorphism because it is the third vertex of a map of distinguished triangles.

## References

* [Stacks Project, Tag 0F16](https://stacks.math.columbia.edu/tag/0F16)
* [Stacks Project, Tag 0EWT](https://stacks.math.columbia.edu/tag/0EWT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w r

namespace Stacks.MayerVietoris.CanonicalMapOfComplexes.General

open MappingCoconeAux

variable {ι : Type*} [Category* ι]
  {A : Type*} [Category* A] [Abelian A]
  {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
  (S : ιᵒᵖ ⥤ (A ⥤ B)) [∀ X : ιᵒᵖ, (S.obj X).Additive] (sq : Square ι)

/-- **The induced map of mapping cocones is a quasi-isomorphism** as soon as the chain map induces
quasi-isomorphisms on the sections over the three corners `X₁, X₂, X₃`: it is the shift of the
third vertex of a map of distinguished triangles whose other two vertices are invertible in the
derived category. -/
theorem quasiIso_mappingCoconeMap {I I' : CochainComplex A ℤ} (f : I ⟶ I')
    [QuasiIso ((complexFunctor S sq.X₁).map f)] [QuasiIso ((complexFunctor S sq.X₂).map f)]
    [QuasiIso ((complexFunctor S sq.X₃).map f)] :
    QuasiIso (mappingCoconeMap S sq f) := by
  have hbip : IsIso (DerivedCategory.Q.map (biprod.map ((complexFunctor S sq.X₃).map f)
      ((complexFunctor S sq.X₂).map f))) :=
    isIso_map_biprod_map DerivedCategory.Q _ _
  have hcomm := (secondMapArrowMap S sq f).w.symm
  have hquasi : QuasiIso (CochainComplex.mappingCone.map (secondMap S sq I) (secondMap S sq I')
      (biprod.map ((complexFunctor S sq.X₃).map f) ((complexFunctor S sq.X₂).map f))
      ((complexFunctor S sq.X₁).map f) hcomm) := by
    rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact Pretriangulated.isIso₃_of_isIso₁₂
      (DerivedCategory.Q.mapTriangle.map
        (CochainComplex.mappingCone.triangleMap (secondMap S sq I) (secondMap S sq I')
          _ _ hcomm))
      (DerivedCategory.mappingCone_triangle_distinguished _)
      (DerivedCategory.mappingCone_triangle_distinguished _) hbip
      (inferInstance : IsIso (DerivedCategory.Q.map ((complexFunctor S sq.X₁).map f)))
  have heq : mappingCoconeMap S sq f = (shiftFunctor (CochainComplex B ℤ) (-1 : ℤ)).map
      (CochainComplex.mappingCone.map _ _ _ _ hcomm) :=
    congrArg (shiftFunctor (CochainComplex B ℤ) (-1 : ℤ)).map
      (mapArrowHom_eq_coneMap _ _ _ (secondMapArrowMap S sq f))
  rw [heq]
  exact (CochainComplex.quasiIso_shift_iff _ _).mpr hquasi

/-- If the sections over the three corners `X₁, X₂, X₃` are carried to quasi-isomorphisms and the
canonical map of the source is a quasi-isomorphism, the canonical map of the target composed with
the map on sections over `X₄` is a quasi-isomorphism. -/
private theorem quasiIso_comp_cSquare {I I' : CochainComplex A ℤ} (f : I ⟶ I')
    [QuasiIso ((complexFunctor S sq.X₁).map f)] [QuasiIso ((complexFunctor S sq.X₂).map f)]
    [QuasiIso ((complexFunctor S sq.X₃).map f)] [QuasiIso (cSquare S sq I)] :
    QuasiIso ((complexFunctor S sq.X₄).map f ≫ cSquare S sq I') := by
  have := quasiIso_mappingCoconeMap S sq f
  rw [cSquare_natural]
  infer_instance

/-- If a chain map induces quasi-isomorphisms on the sections over the four corners, and the
canonical map of its source is a quasi-isomorphism, so is the canonical map of its target. -/
theorem quasiIso_cSquare_of_quasiIso {I I' : CochainComplex A ℤ} (f : I ⟶ I')
    [QuasiIso ((complexFunctor S sq.X₁).map f)] [QuasiIso ((complexFunctor S sq.X₂).map f)]
    [QuasiIso ((complexFunctor S sq.X₃).map f)] [QuasiIso ((complexFunctor S sq.X₄).map f)]
    [QuasiIso (cSquare S sq I)] :
    QuasiIso (cSquare S sq I') := by
  have := quasiIso_comp_cSquare S sq f
  exact quasiIso_of_comp_left ((complexFunctor S sq.X₄).map f) (cSquare S sq I')

/-- If a chain map induces quasi-isomorphisms on the sections over the three corners
`X₁, X₂, X₃`, and the canonical maps of its source and of its target are quasi-isomorphisms, then
it induces a quasi-isomorphism on the sections over `X₄`. -/
theorem quasiIso_complexFunctor_map_of_quasiIso_cSquare {I I' : CochainComplex A ℤ}
    (f : I ⟶ I')
    [QuasiIso ((complexFunctor S sq.X₁).map f)] [QuasiIso ((complexFunctor S sq.X₂).map f)]
    [QuasiIso ((complexFunctor S sq.X₃).map f)]
    [QuasiIso (cSquare S sq I)] [QuasiIso (cSquare S sq I')] :
    QuasiIso ((complexFunctor S sq.X₄).map f) := by
  have := quasiIso_comp_cSquare S sq f
  exact quasiIso_of_comp_right ((complexFunctor S sq.X₄).map f) (cSquare S sq I')

end Stacks.MayerVietoris.CanonicalMapOfComplexes.General

namespace Stacks.MayerVietoris.CanonicalMapOfComplexes

variable {C : Type u} [Category.{w} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}
  [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}] (sq : Square C)

open Stacks.Cohomology.MayerVietoris

omit [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}] in
/-- The sections sequence of a square at the zero sheaf of modules is short exact. -/
lemma shortExact_sectionsShortComplex_of_isZero {M : SheafOfModules.{v} R} (hM : IsZero M) :
    (sectionsShortComplex sq M).ShortExact := by
  have h₁ : IsZero (sectionsShortComplex sq M).X₁ := (sections R sq.X₄).map_isZero hM
  have h₂ : IsZero (sectionsShortComplex sq M).X₂ := by
    have h₃ := (sections R sq.X₃).map_isZero hM
    have h₂ := (sections R sq.X₂).map_isZero hM
    exact biprod_isZero_iff _ _ |>.mpr ⟨h₃, h₂⟩
  have h₃ : IsZero (sectionsShortComplex sq M).X₃ := (sections R sq.X₁).map_isZero hM
  exact { exact := ShortComplex.exact_of_isZero_X₂ _ h₂
          mono_f := h₁.mono _
          epi_g := h₃.epi _ }

/-- **The canonical map of the single complex `M[0]`** of Stacks 0F16 is a quasi-isomorphism
when the sections sequence `M(X) ⟶ M(Z) ⊞ M(Y) ⟶ M(E)` is short exact: in every degree the
sections sequence of `M[0]` is that sequence or zero. -/
theorem quasiIso_cSquare_single (M : SheafOfModules.{v} R)
    (h : (sectionsShortComplex sq M).ShortExact) :
    QuasiIso (cSquare sq ((CochainComplex.singleFunctor (SheafOfModules.{v} R) 0).obj M)) := by
  refine quasiIso_cSquare_of_sectionsShortExact sq _ (fun p ↦ ?_)
  by_cases hp : p = 0
  · subst hp
    have hX : ((CochainComplex.singleFunctor (SheafOfModules.{v} R) 0).obj M).X 0 = M :=
      HomologicalComplex.single_obj_X_self _ _ _
    rw [hX]
    exact h
  · exact shortExact_sectionsShortComplex_of_isZero sq
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M p hp)

/-- **Stacks 0F16 at a sheaf of modules with acyclic corners.** Let `M ⟶ I` be an injective
resolution of a sheaf of modules `M` whose image under the sections functor over each of the four
corners of the square is a quasi-isomorphism. If the sections sequence
`0 ⟶ M(X) ⟶ M(Z) ⊞ M(Y) ⟶ M(E) ⟶ 0` is short exact, the canonical map of Stacks 0F16 at the
K-injective complex `I` is a quasi-isomorphism. -/
theorem quasiIso_cSquare_of_shortExact {M : SheafOfModules.{v} R} (Rs : InjectiveResolution M)
    (h : (sectionsShortComplex sq M).ShortExact)
    [QuasiIso ((sectionsComplex R sq.X₁).map Rs.ι')]
    [QuasiIso ((sectionsComplex R sq.X₂).map Rs.ι')]
    [QuasiIso ((sectionsComplex R sq.X₃).map Rs.ι')]
    [QuasiIso ((sectionsComplex R sq.X₄).map Rs.ι')] :
    QuasiIso (cSquare sq Rs.cochainComplex) := by
  let := HasDerivedCategory.standard AddCommGrpCat.{v}
  have : QuasiIso (General.cSquare (sectionsSystem R) sq
      ((CochainComplex.singleFunctor (SheafOfModules.{v} R) 0).obj M)) :=
    quasiIso_cSquare_single sq M h
  exact General.quasiIso_cSquare_of_quasiIso (sectionsSystem R) sq Rs.ι'

/-- **Acyclicity of the fourth corner, from the canonical map.** Let `M ⟶ I` be an injective
resolution of a sheaf of modules `M` whose image under the sections functor over the corners
`X₁, X₂, X₃` is a quasi-isomorphism, and assume the sections sequence of `M` is short exact. If
the canonical map of Stacks 0F16 at `I` is a quasi-isomorphism, the sections functor over `X₄`
also carries the resolution to a quasi-isomorphism. -/
theorem quasiIso_sections_map_of_quasiIso_cSquare {M : SheafOfModules.{v} R}
    (Rs : InjectiveResolution M) (h : (sectionsShortComplex sq M).ShortExact)
    [QuasiIso ((sectionsComplex R sq.X₁).map Rs.ι')]
    [QuasiIso ((sectionsComplex R sq.X₂).map Rs.ι')]
    [QuasiIso ((sectionsComplex R sq.X₃).map Rs.ι')] [QuasiIso (cSquare sq Rs.cochainComplex)] :
    QuasiIso ((sectionsComplex R sq.X₄).map Rs.ι') := by
  let := HasDerivedCategory.standard AddCommGrpCat.{v}
  have : QuasiIso (General.cSquare (sectionsSystem R) sq
      ((CochainComplex.singleFunctor (SheafOfModules.{v} R) 0).obj M)) :=
    quasiIso_cSquare_single sq M h
  have : QuasiIso (General.cSquare (sectionsSystem R) sq Rs.cochainComplex) :=
    inferInstanceAs (QuasiIso (cSquare sq Rs.cochainComplex))
  exact General.quasiIso_complexFunctor_map_of_quasiIso_cSquare (sectionsSystem R) sq Rs.ι'

section Acyclic

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **Sections over an object carry an injective resolution to a quasi-isomorphism** when the
higher cohomology of the sheaf of modules over that object vanishes: the resolution is then a
quasi-isomorphism between bounded below complexes of objects acyclic for the sections functor. -/
theorem quasiIso_sections_map_ι' [EnoughInjectives (SheafOfModules.{v} R)] (U : C)
    {M : SheafOfModules.{v} R} (Rs : InjectiveResolution M)
    (h : ∀ n : ℕ, 0 < n → IsZero (((sections R U).rightDerived n).obj M)) :
    QuasiIso ((sectionsComplex R U).map Rs.ι') := by
  let := HasDerivedCategory.standard (SheafOfModules.{v} R)
  let := HasDerivedCategory.standard AddCommGrpCat.{v}
  have : PreservesFiniteLimits (SheafOfModules.toSheaf.{v} R) := inferInstance
  have : PreservesFiniteLimits ((sheafSections J AddCommGrpCat.{v}).obj (op U)) :=
    inferInstanceAs (PreservesFiniteLimits
      (sheafToPresheaf J AddCommGrpCat.{v} ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{v}).obj (op U)))
  have hM : (sections R U).rightAcyclic M :=
    (Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat (sections R U) M).mpr h
  refine Functor.quasiIso_mapHomologicalComplex_of_rightAcyclic (sections R U) Rs.ι'
    ((CochainComplex.plus_iff _ _).mpr ⟨0, inferInstance⟩)
    ((CochainComplex.plus_iff _ _).mpr ⟨0, inferInstance⟩) (fun n ↦ ?_)
    (fun n ↦ Functor.rightAcyclic_of_injective _ _)
  by_cases hn : n = 0
  · subst hn
    have hX : ((CochainComplex.singleFunctor (SheafOfModules.{v} R) 0).obj M).X 0 = M :=
      HomologicalComplex.single_obj_X_self _ _ _
    rw [hX]
    exact hM
  · have : Injective (((CochainComplex.singleFunctor (SheafOfModules.{v} R) 0).obj M).X n) :=
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M n hn).injective
    exact Functor.rightAcyclic_of_injective _ _

end Acyclic

section Derived

-- `Stacks.MayerVietoris.CanonicalMapOfComplexes.derivedCSquareData`
-- (`DerivedCanonicalMapAndTriangle.lean:1383`) is built over the standard model of the derived
-- category, so the condition of Stacks 0F16 below is stated against that model.
attribute [local instance] HasDerivedCategory.standard

variable [UnivLE.{u, v}] [UnivLE.{w, v}] [UnivLE.{r, v}]

/-- **The condition of Stacks 0F16 at a sheaf of modules placed in degree zero** is the
quasi-isomorphism property of the canonical map at the extension of any injective resolution of
it, which is a K-injective representative. -/
theorem isCSquareIso_singleFunctor_obj_iff (M : SheafOfModules.{v} R)
    (Rs : InjectiveResolution M) :
    (derivedCSquareData.{u, v} (R := R) sq).IsCSquareIso
        ((DerivedCategory.singleFunctor (SheafOfModules.{v} R) 0).obj M) ↔
      QuasiIso (cSquare sq Rs.cochainComplex) := by
  have : IsIso (DerivedCategory.Q.map Rs.ι') :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr inferInstance
  exact (derivedCSquareData.{u, v} (R := R) sq).isCSquareIso_iff_quasiIso _ Rs.cochainComplex
    ((asIso (DerivedCategory.Q.map Rs.ι')).symm ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (SheafOfModules.{v} R) 0).app M).symm)

end Derived

end Stacks.MayerVietoris.CanonicalMapOfComplexes
