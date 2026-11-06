module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Subobject
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Subobject.Lattice
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeExtension
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.LocalGeneration
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentClosure
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentKernelsOnSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeFromGlobalGenerators
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite
import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsUnconditional

/-!
# Quasi-coherent modules on an algebraic space as colimits of finite type submodules

Stacks 0829 asserts that on a quasi-compact and quasi-separated algebraic space every
quasi-coherent `𝒪_F`-module is the directed colimit of its quasi-coherent submodules of finite
type.  This file builds the system of those submodules, proves that it is directed, and reduces
the colimit assertion to the filtered presentation by finitely presented modules which
Stacks 07V9 supplies.

A submodule is a categorical `CategoryTheory.Subobject` of the module, so that two submodules
with the same image are equal, and the system of those satisfying a property is the
corresponding `CategoryTheory.ObjectProperty.FullSubcategory`; its morphisms are the
inclusions, which is what makes the canonical cocone well defined.  This is the same
formulation as the scheme case of the statement, Stacks 01PG, in
`StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeSubobjects` and
`...FiniteTypeSubobjectColimit`; nothing of that file is reused, because quasi-coherence there
is Mathlib's `SheafOfModules.IsQuasicoherent` on the Zariski site of a scheme, whereas here it
is `SheafOfModules.IsQuasicoherentOnSite` on the small étale site of an algebraic space.

## Main definitions

* `AlgebraicGeometry.Space.finiteTypeQuasicoherentSubobjectProperty` is the property of a
  subobject of `F` that its underlying module is quasi-coherent and of finite type.
* `AlgebraicGeometry.Space.FiniteTypeQuasicoherentSubobject` is the category of such
  subobjects,
  `AlgebraicGeometry.Space.finiteTypeQuasicoherentSubobjectFunctor` the diagram they form and
  `AlgebraicGeometry.Space.finiteTypeQuasicoherentSubobjectCocone` its canonical cocone with
  point `F`.

## Main results

* `AlgebraicGeometry.Space.finiteTypeQuasicoherentSubobject_isFiltered`: **the directedness
  assertion of Stacks 0829**, for an arbitrary quasi-coherent module on an arbitrary algebraic
  space.
* `AlgebraicGeometry.Space.nonempty_isColimit_finiteTypeQuasicoherentSubobjectCocone`: **the
  whole of the source's argument for the colimit assertion of Stacks 0829**, with the filtered
  diagram of finitely presented modules taken as data rather than obtained from Stacks 07V9.
* `SheafOfModules.isGrothendieckAbelian_of_essentiallySmall`: the sheaves of modules on an
  essentially small site form a Grothendieck abelian category at the universe of its small
  model.  Mathlib's instance covers only a site which is small on the nose.  This discharges
  the `LocallySmall` hypothesis of
  `AlgebraicGeometry.Space.quasicoherentSheaves_isGrothendieckAbelian_of_closure` at the module
  universe `u`, which that file's notes describe as unavailable there.
* `AlgebraicGeometry.Space.isColimit_finiteTypeQuasicoherentSubobjectCocone`: **the colimit
  assertion of Stacks 0829**, conditional on Stacks 07V9; the unconditional form, which carries
  the registration, is
  `AlgebraicGeometry.Space.nonempty_isColimit_finiteTypeQuasicoherentSubobjectCocone_of_qcqs`.

## Implementation notes

The source's proof of the directedness assertion is: the image in `F` of the direct sum of two
finite type quasi-coherent submodules is again one.  That needs three closure properties of the
two conditions, all three of them theorems of this tree.

* The direct sum of two quasi-coherent modules is quasi-coherent.  This is unconditional:
  `SheafOfModules.IsQuasicoherentOnSite.biprod` asks only for restriction-stability of global
  presentations, which is `Stacks.SheafOfModules.hasGlobalPresentation_overMap`.
* The direct sum of two modules of finite type is of finite type.  This is unconditional and is
  proved here, by refining the two covering families against each other and restricting both
  generating families with `Stacks.SheafOfModules.generatingSectionsOverMap`.  The route used
  for the scheme case — the direct sum is a split extension and
  `Stacks.SheafOfModules.isFiniteType_middle_of_shortExact` — is not available, that statement
  being proved only over a topological space.
* The image of a morphism of quasi-coherent modules is quasi-coherent.  In an abelian category
  the image is a kernel of a cokernel, so this needs quasi-coherence to be closed under kernels
  and under cokernels — the kernel and cokernel halves of clause (3) of Stacks 03M1.  The kernel
  half is `AlgebraicGeometry.Space.isClosedUnderKernels_quasicoherentSheaves`, applied to
  Descent, Proposition 03DX(2), which is
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_isCartesianOnAffineCharts`; the cokernel
  half is `AlgebraicGeometry.Space.isClosedUnderCokernels_quasicoherentSheaves`, in the
  `CategoryTheory.ObjectProperty.IsClosedUnderCokernels` shape in which
  `AlgebraicGeometry.Space.quasicoherentSheaves_abelian_of_closure` and
  `AlgebraicGeometry.Space.isQuasicoherent_colimit` ask for it.

The directedness assertion is therefore unconditional.

For the colimit assertion the source writes `F` as a filtered colimit of finitely presented
quasi-coherent modules by Stacks 07V9 and takes the images of the stages.  Stacks 07V9 is
`AlgebraicGeometry.Space.exists_isFilteredColimit_isFinitePresentationOnSite`, in a module which
imports this one, so here it is carried as the hypothesis `h07V9`, stated for the given space
and module.  Two further
ingredients are proved here and are unconditional: that the modules on the small étale ringed
site of an algebraic space form a Grothendieck abelian category at the universe of the schemes,
which follows from essential smallness of that site by transport along its small model, and
that in a Grothendieck abelian category a filtered family of subobjects with supremum `⊤`
exhibits the ambient object as its colimit.  The last ingredient, that a finitely presented
module is of finite type, is Stacks 03DL(7) implies 03DL(5) in a form that compares
`SheafOfModules.IsFinitePresentationOnSite` with Mathlib's `SheafOfModules.IsFiniteType`, and
is also unconditional: the tree's
`SheafOfModules.isFiniteTypeOnSite_of_isFinitePresentationOnSite` gives the categorical form
of 03DL(5), and `Stacks.SheafOfModules.isFiniteType_of_isFiniteTypeOnSite` descends it to
Mathlib's predicate across the universe lift `SheafOfModules.uliftForPresentation`.

The module universe is **not** free and is the universe `u` of the schemes.  This is forced by
Mathlib's `SheafOfModules.IsFiniteType`, which is defined only for a module universe equal to
the universe of the coefficient ring sheaf, and the structure sheaf of the small étale ringed
site of an algebraic space over `Scheme.{u}` is `CommRingCat.{u}`-valued.  It is not forced by
the sheafification instances, which hold both at `u` and at every universe at least `u + 1`.

## References

* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
* [Stacks Project, Tag 07V9](https://stacks.math.columbia.edu/tag/07V9)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 01PG](https://stacks.math.columbia.edu/tag/01PG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Space

section Epi

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]


variable [HasSheafify J AddCommGrpCat.{u}]



variable [∀ Z : C, HasWeakSheafify (J.over Z) AddCommGrpCat.{u}]
  [∀ Z : C, (J.over Z).WEqualsLocallyBijective AddCommGrpCat.{u}]


omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify J AddCommGrpCat.{u}] in
/-- A zero sheaf of modules is of finite type: the empty family of sections generates it over
every object of the site, every morphism into a zero object being an epimorphism. -/
private lemma isFiniteType_of_isZero {M : SheafOfModules.{u} R} (hM : IsZero M) :
    M.IsFiniteType :=
  ⟨⟨{ I := C
      X := id
      coversTop := fun _ => GrothendieckTopology.covering_of_eq_top J (by simp)
      generators := fun Z =>
        { I := PEmpty.{u + 1}
          s := fun i => i.elim
          epi := ⟨fun g h _ => (SheafOfModules.isZero_over hM Z).eq_of_src g h⟩ } },
    ⟨fun _ => ⟨by infer_instance⟩⟩⟩⟩


end Epi


section Biprod

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{u}]
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{u}]
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Restriction to a slice of the site preserves a binary product of sheaves of modules: it is
computed sectionwise, and the inclusion of sheaves of modules into presheaves of modules
reflects limits. -/
private lemma overFunctor_preservesLimit_pair {M N : SheafOfModules.{u} R} (U : C) :
    PreservesLimit (pair M N) (SheafOfModules.overFunctor R U) := by
  classical
  refine ⟨fun {c} hc => ?_⟩
  let E := SheafOfModules.overFunctor R U
  let c' := E.mapCone c
  have hforget : IsLimit ((SheafOfModules.forget (R.over U)).mapCone c') := by
    apply PresheafOfModules.evaluationJointlyReflectsLimits
    intro V
    let V' : Cᵒᵖ := Opposite.op ((Over.forget U).obj V.unop)
    have h := isLimitOfPreserves (SheafOfModules.evaluation R V') hc
    have h' := isLimitOfPreserves
      (ModuleCat.restrictScalars (RingHom.id ((R.obj).obj V'))) h
    change IsLimit ((ModuleCat.restrictScalars (RingHom.id ((R.obj).obj V'))).mapCone
      ((SheafOfModules.evaluation R V').mapCone c))
    exact h'
  exact ⟨isLimitOfReflects (SheafOfModules.forget (R.over U)) hforget⟩

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The direct sum of two sheaves of modules of finite type is of finite type.

The two covering families are refined against each other: an object of the refinement comes
with a morphism to a member of each, along which both generating families restrict, and the
sum of the two restricted families generates the direct sum because restriction to a slice
preserves it. -/
private lemma isFiniteType_biprod {M N : SheafOfModules.{u} R} [HasBinaryBiproduct M N]
    [M.IsFiniteType] [N.IsFiniteType] : (M ⊞ N).IsFiniteType := by
  classical
  obtain ⟨p, hp⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData M
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData N
  let I := Σ Z : C, Σ i : p.I, Σ j : q.I, (Z ⟶ p.X i) × (Z ⟶ q.X j)
  let W : I → C := fun ij => ij.1
  have hW : J.CoversTop W := by
    intro Z
    refine J.superset_covering ?_ (J.intersection_covering (p.coversTop Z) (q.coversTop Z))
    intro T f hf
    rcases hf with ⟨hfM, hfN⟩
    obtain ⟨i, ⟨fM⟩⟩ := (Sieve.mem_ofObjects_iff p.X f).mp hfM
    obtain ⟨j, ⟨fN⟩⟩ := (Sieve.mem_ofObjects_iff q.X f).mp hfN
    rw [Sieve.mem_ofObjects_iff]
    exact ⟨⟨T, i, j, ⟨fM, fN⟩⟩, ⟨𝟙 T⟩⟩
  let genAt (ij : I) :
      {g : ((M ⊞ N).over (W ij)).GeneratingSections // g.IsFiniteType} := by
    rcases ij with ⟨Z, i, j, fM, fN⟩
    change {g : ((M ⊞ N).over Z).GeneratingSections // g.IsFiniteType}
    have : (p.generators i).IsFiniteType := hp.isFiniteType i
    have : (q.generators j).IsFiniteType := hq.isFiniteType j
    let sM := Stacks.SheafOfModules.generatingSectionsOverMap M fM (p.generators i)
    let sN := Stacks.SheafOfModules.generatingSectionsOverMap N fN (q.generators j)
    have : sM.IsFiniteType := ⟨by change Finite (p.generators i).I; infer_instance⟩
    have : sN.IsFiniteType := ⟨by change Finite (q.generators j).I; infer_instance⟩
    let Rw := R.over Z
    haveI : ∀ J : Type u, HasColimitsOfShape (Discrete J) (PresheafOfModules.{u} Rw.obj) :=
      fun J => PresheafOfModules.hasColimitsOfShape _ _
    haveI : HasColimitsOfSize.{u, u} (PresheafOfModules.{u} Rw.obj) := inferInstance
    haveI : HasColimitsOfSize.{u, u} (SheafOfModules.{u} Rw) := inferInstance
    haveI : HasCoproducts.{u} (SheafOfModules.{u} Rw) :=
      fun J => HasColimitsOfSize.has_colimits_of_shape (Discrete J)
    haveI : HasCountableCoproducts (SheafOfModules.{u} Rw) :=
      hasCountableCoproducts_of_hasCoproducts _
    haveI : HasFiniteCoproducts (SheafOfModules.{u} Rw) := hasFiniteCoproducts_of_hasCoproducts _
    let E := SheafOfModules.overFunctor R Z
    have : E.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
    haveI : PreservesLimit (pair M N) E := overFunctor_preservesLimit_pair Z
    haveI : PreservesBinaryBiproduct M N E :=
      preservesBinaryBiproduct_of_preservesBinaryProduct E
    let e := E.mapBiprod M N
    haveI : HasBinaryBiproduct (M.over Z) (N.over Z) := inferInstance
    haveI : IsIso e.inv := by infer_instance
    let p0 : SheafOfModules.free (R := Rw) (Sum sM.I sN.I) ⟶ (M ⊞ N).over Z :=
      (SheafOfModules.freeSumIso (R := Rw) sM.I sN.I).inv ≫
        (biprod.isoCoprod _ _).inv ≫ biprod.map sM.π sN.π ≫ e.inv
    have hp0 : Epi p0 := by infer_instance
    let τ : ((M ⊞ N).over Z).GeneratingSections :=
      { I := Sum sM.I sN.I
        s := ((M ⊞ N).over Z).freeHomEquiv p0
        epi := by
          rw [((M ⊞ N).over Z).freeHomEquiv.symm_apply_apply]
          exact hp0 }
    exact ⟨τ, ⟨inferInstanceAs (Finite (Sum sM.I sN.I))⟩⟩
  exact ⟨⟨{ I := I, X := W, coversTop := hW, generators := fun ij => (genAt ij).val },
    ⟨fun ij => (genAt ij).property⟩⟩⟩

end Biprod

end AlgebraicGeometry.Space

namespace SheafOfModules

section Grothendieck

/-- The sheaves of modules over a sheaf of rings on an essentially small site form a
Grothendieck abelian category at the universe of the small model.

Mathlib's instance is stated for a site which is small on the nose; this transports it along
the equivalence with the small model, which carries the topology to its induced topology and
the sheaves of modules to the sheaves of modules over the pushforward ring sheaf.

The three universes are independent: `C` lives in `Type v` with `Category.{w} C`, while the
ring sheaf, the modules and the Grothendieck axioms are all at the small model's universe `u`.
That is what makes this usable at the small étale site of an algebraic space, whose objects
live in `Type (u + 1)` while its structure sheaf is `CommRingCat.{u}`-valued.

This is the `SheafOfModules` analogue of, and not to be confused with, Mathlib's
`CategoryTheory.Sheaf.isGrothendieckAbelian_of_essentiallySmall`, which is about `Sheaf J A`
for an abelian coefficient category `A`.  The two share a bare name. -/
@[sga "4 II 6.7" "special case"]
theorem isGrothendieckAbelian_of_essentiallySmall {C : Type v} [Category.{w} C]
    [EssentiallySmall.{u} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u} R) := by
  let e := (equivSmallModel.{u} C).symm
  let K := e.functor.inducedTopology J
  have : e.inverse.IsDenseSubsite J K :=
    inferInstanceAs (e.symm.functor.IsDenseSubsite J (e.symm.inverse.inducedTopology J))
  let T := (e.functor.sheafPushforwardContinuous RingCat.{u} K J).obj R
  let φ : T ⟶ (e.functor.sheafPushforwardContinuous RingCat.{u} K J).obj R := 𝟙 T
  let ψ : R ⟶ (e.inverse.sheafPushforwardContinuous RingCat.{u} J K).obj T :=
    ⟨Functor.whiskerRight (NatTrans.op e.counit) R.obj⟩
  let E := SheafOfModules.pushforwardPushforwardEquivalence.{u} e φ ψ
    (by
      change _ = _ ≫ 𝟙 _
      exact (Category.comp_id _).symm) (by
      ext U : 2
      dsimp [φ, ψ, T]
      simp only [Category.id_comp]
      change R.obj.map (e.counit.app (e.functor.obj U.unop)).op ≫
        R.obj.map (e.functor.map (e.unit.app U.unop)).op = 𝟙 _
      rw [← R.obj.map_comp, ← op_comp]
      exact (congrArg (fun f => R.obj.map f.op)
        (e.functor_unit_comp U.unop)).trans (R.obj.map_id _))
  exact IsGrothendieckAbelian.of_equivalence E.symm

end Grothendieck

end SheafOfModules

namespace AlgebraicGeometry.Space

section Subobjects

variable {C : Type v} [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{u} C]

/-- The images of the legs of a colimit cocone have supremum the whole of its point: the
inclusion of that supremum is an epimorphism because every leg factors through it, and it is a
monomorphism because it is a subobject arrow. -/
lemma iSup_imageSubobject_eq_top_of_isColimit {I : Type u} [SmallCategory I]
    {D : I ⥤ C} {F : C} (φ : D ⟶ (Functor.const I).obj F)
    (hc : IsColimit (Cocone.mk F φ)) :
    (⨆ i, imageSubobject (φ.app i)) = ⊤ := by
  classical
  let T : Subobject F := ⨆ i, imageSubobject (φ.app i)
  let q : (T : C) ⟶ F := T.arrow
  have hq : Epi q := by
    refine ⟨fun {Z} g h hh => ?_⟩
    apply hc.hom_ext
    intro i
    let G : Subobject F := imageSubobject (φ.app i)
    have hfac : φ.app i = factorThruImageSubobject (φ.app i) ≫ G.arrow :=
      (imageSubobject_arrow_comp (φ.app i)).symm
    have hle : G ≤ T := le_iSup (fun j => imageSubobject (φ.app j)) i
    let k : (G : C) ⟶ (T : C) := Subobject.ofLE G T hle
    have hk : G.arrow = k ≫ q := (Subobject.ofLE_arrow _).symm
    let l : D.obj i ⟶ (T : C) := factorThruImageSubobject (φ.app i) ≫ k
    have hφ : φ.app i = l ≫ q := by simpa only [l, Category.assoc, ← hk] using hfac
    simp only [hφ, Category.assoc, hh]
  have : Epi q := hq
  have : Mono q := by dsimp [q]; infer_instance
  have : IsIso q := isIso_of_mono_of_epi q
  simpa only [T, q, Subobject.mk_arrow] using Subobject.mk_eq_top_of_isIso q

/-- In a Grothendieck abelian category, a filtered family of subobjects of `F` whose supremum
is `⊤` exhibits `F` as its colimit.

This is `CategoryTheory.IsGrothendieckAbelian.isColimitMapCoconeOfSubobjectMkEqISup`,
transported from the small model of the index category, which exists because a Grothendieck
abelian category is well-powered. -/
noncomputable def isColimitSubobjectCocone_of_iSup_eq_top {F : C}
    (P : ObjectProperty (Subobject F)) [IsFiltered P.FullSubcategory]
    (h : (⨆ G : P.FullSubcategory, G.obj) = (⊤ : Subobject F)) :
    IsColimit (Cocone.mk F
      (show (P.ι ⋙ Subobject.underlying) ⟶ (Functor.const P.FullSubcategory).obj F from
        { app := fun G => G.obj.arrow
          naturality := by
            intro G H f
            change Subobject.underlying.map f.hom ≫ H.obj.arrow = G.obj.arrow ≫ 𝟙 F
            rw [Category.comp_id]
            exact Subobject.underlying_arrow f.hom })) := by
  classical
  let D : P.FullSubcategory ⥤ MonoOver F := P.ι ⋙ Subobject.representative
  let c : Cocone (D ⋙ MonoOver.forget F) :=
    Cocone.mk (Over.mk (𝟙 F))
      { app := fun G => Over.homMk G.obj.arrow
        naturality := by
          intro G H f
          apply Over.OverMorphism.ext
          change Subobject.underlying.map f.hom ≫ H.obj.arrow = G.obj.arrow ≫ 𝟙 F
          simp }
  have : ObjectProperty.Small.{u} P := inferInstance
  let e := equivSmallModel.{u} P.FullSubcategory
  have : IsFiltered (SmallModel.{u} P.FullSubcategory) := IsFiltered.of_equivalence e
  have hs : (⨆ i, (e.inverse.obj i).obj) = (⊤ : Subobject F) := by
    rw [← h]
    refine le_antisymm (iSup_le fun i => le_iSup _ (e.inverse.obj i)) (iSup_le fun G => ?_)
    have hle : G.obj ≤ (e.inverse.obj (e.functor.obj G)).obj :=
      leOfHom ((e.unitIso.app G).hom.hom)
    exact hle.trans (le_iSup (fun i : SmallModel.{u} P.FullSubcategory =>
      (e.inverse.obj i).obj) (e.functor.obj G))
  have : Mono (c.whisker e.inverse).pt.hom := by
    change Mono (𝟙 F)
    infer_instance
  have hc := IsGrothendieckAbelian.isColimitMapCoconeOfSubobjectMkEqISup
    (e.inverse ⋙ D) (c.whisker e.inverse) (by
      change Subobject.mk (𝟙 F) = ⨆ i, Subobject.mk (e.inverse.obj i).obj.arrow
      simpa only [Subobject.mk_eq_top_of_isIso, Subobject.mk_arrow] using hs.symm)
  exact IsColimit.ofWhiskerEquivalence e.symm hc

end Subobjects

section Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)

/-- The image of a morphism of quasi-coherent `𝒪_F`-modules is quasi-coherent, granted that
quasi-coherence is closed under kernels and under cokernels: in an abelian category the image
is the kernel of the cokernel projection. -/
lemma isQuasicoherentOnSite_image {M N : Modules.{u, u} B S hS X hX}
    (hker : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O))).IsClosedUnderKernels)
    (hcoker : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O))).IsClosedUnderCokernels)
    (f : M ⟶ N) (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) :
    (Subobject.underlying.obj (imageSubobject f)).IsQuasicoherentOnSite := by
  have := hker
  have := hcoker
  have hcok : (cokernel f).IsQuasicoherentOnSite := ObjectProperty.prop_cokernel _ f hM hN
  have hk : (kernel (cokernel.π f)).IsQuasicoherentOnSite :=
    ObjectProperty.prop_kernel _ (cokernel.π f) hN hcok
  exact ObjectProperty.prop_of_iso _
    ((Abelian.imageIsoImage f).trans (imageSubobjectIso f).symm) hk

set_option synthInstance.maxHeartbeats 200000 in
/-- The image of a morphism out of an `𝒪_F`-module of finite type is of finite type: it is a
quotient of the source. -/
private lemma isFiniteType_imageSubobject {M N : Modules.{u, u} B S hS X hX} (f : M ⟶ N)
    (hM : M.IsFiniteType) :
    (Subobject.underlying.obj (imageSubobject f)).IsFiniteType := by
  have : Epi (factorThruImageSubobject f) := by
    dsimp [factorThruImageSubobject]
    apply epi_comp
  exact Stacks.SheafOfModules.isFiniteType_of_epi
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O))
    (factorThruImageSubobject f) hM

/-- The property of a subobject of `F` being a finite type quasi-coherent module. -/
def finiteTypeQuasicoherentSubobjectProperty (F : Modules.{u, u} B S hS X hX) :
    ObjectProperty (Subobject F) :=
  fun G => SheafOfModules.IsQuasicoherentOnSite (G : Modules.{u, u} B S hS X hX) ∧
    SheafOfModules.IsFiniteType (G : Modules.{u, u} B S hS X hX)

/-- The image of a morphism from a finite type quasi-coherent module to a quasi-coherent module
is a finite type quasi-coherent subobject. -/
private lemma finiteTypeQuasicoherentSubobjectProperty_imageSubobject
    {M F : Modules.{u, u} B S hS X hX} (f : M ⟶ F) (hM : M.IsQuasicoherentOnSite)
    (hF : F.IsQuasicoherentOnSite) (hMf : M.IsFiniteType) :
    finiteTypeQuasicoherentSubobjectProperty B S hS X hX F (imageSubobject f) :=
  ⟨isQuasicoherentOnSite_image B S hS X hX
      (isClosedUnderKernels_quasicoherentSheaves B S hS X hX
        (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS X hX))
      (isClosedUnderCokernels_quasicoherentSheaves B S hS X hX) f hM hF,
    isFiniteType_imageSubobject B S hS X hX f hMf⟩

/-- The category of finite type quasi-coherent subobjects of `F`. -/
abbrev FiniteTypeQuasicoherentSubobject (F : Modules.{u, u} B S hS X hX) :=
  (finiteTypeQuasicoherentSubobjectProperty B S hS X hX F).FullSubcategory

/-- The diagram of all finite type quasi-coherent subobjects of `F`. -/
noncomputable def finiteTypeQuasicoherentSubobjectFunctor (F : Modules.{u, u} B S hS X hX) :
    FiniteTypeQuasicoherentSubobject B S hS X hX F ⥤ Modules.{u, u} B S hS X hX :=
  (finiteTypeQuasicoherentSubobjectProperty B S hS X hX F).ι ⋙ Subobject.underlying

/-- The canonical cocone given by the inclusions of finite type quasi-coherent submodules. -/
noncomputable def finiteTypeQuasicoherentSubobjectCocone (F : Modules.{u, u} B S hS X hX) :
    Cocone (finiteTypeQuasicoherentSubobjectFunctor B S hS X hX F) :=
  Cocone.mk F
    { app := fun G => G.obj.arrow
      naturality := fun {_ _} f => Subobject.underlying_arrow f.hom }

/-- The finite type quasi-coherent submodules of a quasi-coherent module form a directed
system. -/
@[stacks 0829 "the directedness clause, for an arbitrary quasi-coherent module on an arbitrary \
algebraic space"]
theorem finiteTypeQuasicoherentSubobject_isFiltered
    (F : Modules.{u, u} B S hS X hX) [F.IsQuasicoherentOnSite] :
    IsFiltered (FiniteTypeQuasicoherentSubobject B S hS X hX F) := by
  classical
  let P := finiteTypeQuasicoherentSubobjectProperty B S hS X hX F
  have hres : ∀ (M : Modules.{u, u} B S hS X hX)
      {Y Z : (smallEtaleRingedSite B S hS X hX).C}, (Y ⟶ Z) →
      (M.over Z).HasGlobalPresentation → (M.over Y).HasGlobalPresentation := by
    intro M Y Z f h
    exact Stacks.SheafOfModules.hasGlobalPresentation_overMap M f h
  have hsh : ∀ U : (smallEtaleRingedSite B S hS X hX).C,
      HasSheafify ((smallEtaleRingedSite B S hS X hX).J.over U) AddCommGrpCat.{u} := by
    change ∀ U : SmallEtale B S hS X,
      HasSheafify ((SmallEtale.topology B S hS X).over U) AddCommGrpCat.{u}
    infer_instance
  refine { cocone_objs := ?_, cocone_maps := ?_, nonempty := ?_ }
  · intro A D
    have hAq : (A.1 : Modules.{u, u} B S hS X hX).IsQuasicoherentOnSite := A.2.1
    have hDq : (D.1 : Modules.{u, u} B S hS X hX).IsQuasicoherentOnSite := D.2.1
    have : (A.1 : Modules.{u, u} B S hS X hX).IsFiniteType := A.2.2
    have : (D.1 : Modules.{u, u} B S hS X hX).IsFiniteType := D.2.2
    have : HasBinaryBiproduct (A.1 : Modules.{u, u} B S hS X hX)
      (D.1 : Modules.{u, u} B S hS X hX) := inferInstance
    have hsumq : ((A.1 : Modules.{u, u} B S hS X hX) ⊞
        (D.1 : Modules.{u, u} B S hS X hX)).IsQuasicoherentOnSite :=
      SheafOfModules.IsQuasicoherentOnSite.biprod hres hAq hDq
    have hsumf : ((A.1 : Modules.{u, u} B S hS X hX) ⊞
        (D.1 : Modules.{u, u} B S hS X hX)).IsFiniteType := isFiniteType_biprod
    let f : (A.1 : Modules.{u, u} B S hS X hX) ⊞ (D.1 : Modules.{u, u} B S hS X hX) ⟶ F :=
      biprod.desc A.1.arrow D.1.arrow
    let I : Subobject F := imageSubobject f
    have hle : ∀ (G : Subobject F) (ι : (G : Modules.{u, u} B S hS X hX) ⟶ _),
        ι ≫ f = G.arrow → G ≤ I := fun G ι h => by
      apply Subobject.le_of_comm (ι ≫ factorThruImageSubobject f)
      change (ι ≫ factorThruImageSubobject f) ≫ I.arrow = G.arrow
      rw [Category.assoc, imageSubobject_arrow_comp, h]
    exact ⟨⟨I, finiteTypeQuasicoherentSubobjectProperty_imageSubobject B S hS X hX f hsumq ‹_›
        hsumf⟩,
      P.homMk (homOfLE (hle _ biprod.inl (by simp [f]))),
      P.homMk (homOfLE (hle _ biprod.inr (by simp [f]))), trivial⟩
  · intro A D f g
    refine ⟨D, 𝟙 D, ?_⟩
    simp only [Category.comp_id]
    apply P.hom_ext
    exact Subsingleton.elim _ _
  · have hz : IsZero ((⊥ : Subobject F) : Modules.{u, u} B S hS X hX) :=
      IsZero.of_iso (isZero_zero _) Subobject.botCoeIsoZero
    exact ⟨⟨⊥, SheafOfModules.IsQuasicoherentOnSite.of_isZero hz,
      isFiniteType_of_isZero hz⟩⟩

/-- **The colimit clause of Stacks 0829 from a filtered presentation by finitely presented
modules.**  Given a filtered diagram of finitely presented `𝒪_F`-modules with colimit `F`, the
canonical cocone of the finite type quasi-coherent submodules of `F` is a colimit cocone.

This is the whole of the source's argument for the colimit clause; the diagram is what Stacks
07V9 supplies. -/
lemma nonempty_isColimit_finiteTypeQuasicoherentSubobjectCocone
    (F : Modules.{u, u} B S hS X hX) [F.IsQuasicoherentOnSite]
    (I : Type u) [instI : SmallCategory I] [_instF : IsFiltered I]
    (D : I ⥤ Modules.{u, u} B S hS X hX) (φ : D ⟶ (Functor.const I).obj F)
    (hfp : ∀ i, (D.obj i).IsFinitePresentationOnSite)
    (hcol : IsColimit (Cocone.mk F φ)) :
    Nonempty (IsColimit (finiteTypeQuasicoherentSubobjectCocone B S hS X hX F)) := by
  classical
  have hes : EssentiallySmall.{u} (smallEtaleRingedSite B S hS X hX).C := by
    change EssentiallySmall.{u} (SmallEtale B S hS X)
    infer_instance
  have hgr : IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS X hX) :=
    SheafOfModules.isGrothendieckAbelian_of_essentiallySmall _
  have hfiltered : IsFiltered (FiniteTypeQuasicoherentSubobject B S hS X hX F) :=
    finiteTypeQuasicoherentSubobject_isFiltered B S hS X hX F
  have himg := iSup_imageSubobject_eq_top_of_isColimit φ hcol
  have htop : (⨆ G : FiniteTypeQuasicoherentSubobject B S hS X hX F, G.obj) =
      (⊤ : Subobject F) := by
    refine le_antisymm le_top ?_
    rw [← himg]
    refine iSup_le fun i => ?_
    have hfi : (D.obj i).IsFiniteType :=
      Stacks.SheafOfModules.isFiniteType_of_isFiniteTypeOnSite _ inferInstance
    exact le_iSup (fun G : FiniteTypeQuasicoherentSubobject B S hS X hX F => G.obj)
      ⟨imageSubobject (φ.app i), finiteTypeQuasicoherentSubobjectProperty_imageSubobject
        B S hS X hX (φ.app i) inferInstance ‹_› hfi⟩
  exact ⟨isColimitSubobjectCocone_of_iSup_eq_top
    (finiteTypeQuasicoherentSubobjectProperty B S hS X hX F) htop⟩

/-- A quasi-coherent module on a quasi-compact, quasi-separated algebraic space is the
colimit of the canonical diagram of its finite type quasi-coherent submodules, granted Stacks
07V9 for that space as the hypothesis `h07V9`.

This is the 07V9-conditional form of the colimit clause of Stacks 0829; Stacks 07V9 is proved
only in a module which imports this one.  The full form, with no hypothesis beyond the source's,
is `AlgebraicGeometry.Space.nonempty_isColimit_finiteTypeQuasicoherentSubobjectCocone_of_qcqs`,
which carries the registration. -/
noncomputable def isColimit_finiteTypeQuasicoherentSubobjectCocone
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hqc : IsQuasiCompactSpace B S hS X)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (h07V9 : IsQuasiCompactSpace B S hS X → IsAbsolutelyQuasiSeparated B S hS hZ X →
      ∀ G : Modules.{u, u} B S hS X hX, G.IsQuasicoherentOnSite →
        ∃ (I : Type u) (inst : SmallCategory I),
          let _ := inst
          ∃ (_ : IsFiltered I) (D : I ⥤ Modules.{u, u} B S hS X hX)
            (φ : D ⟶ (Functor.const I).obj G),
            (∀ i, (D.obj i).IsFinitePresentationOnSite) ∧
              Nonempty (IsColimit (Cocone.mk G φ)))
    (F : Modules.{u, u} B S hS X hX) [F.IsQuasicoherentOnSite] :
    IsColimit (finiteTypeQuasicoherentSubobjectCocone B S hS X hX F) := by
  classical
  refine Classical.choice ?_
  obtain ⟨I, inst, hfil, D, φ, hfp, hcol⟩ := h07V9 hqc hqs F ‹_›
  exact nonempty_isColimit_finiteTypeQuasicoherentSubobjectCocone
    B S hS X hX F I (instI := inst) (_instF := hfil) D φ hfp hcol.some

end Space

end AlgebraicGeometry.Space


end
