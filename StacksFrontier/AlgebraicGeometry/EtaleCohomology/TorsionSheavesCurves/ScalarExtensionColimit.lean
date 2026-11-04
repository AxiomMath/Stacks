module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import StacksCore.Tactic.StacksAttribute
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.RestrictionComposition
public import StacksFrontier.AlgebraicGeometry.FieldExtensionDescent.Limit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BasePasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PropertyAPushforward
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.Homology.Ext.MapExactFunctorComp
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ScalarExtension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ConstantSmoothCurveInputs
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.AlgebraColimitCohomology
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.FGSubalgebraBaseChangeSupplement
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeCurveSupplement

/-!
# Elements of a filtered colimit of abelian groups that vanish

In a filtered colimit of abelian groups, an element of a stage whose image in the colimit is zero
is already zero at a later stage. This is the form in which Tag 03Q6 (the cohomology of a limit of
schemes is the colimit of the cohomology of the stages) is used for the scalar extension of
Tag 0A58: a class on `X` that dies on `X_{k'}` dies on `X_A` for a finitely generated
`k`-subalgebra `A` of `k'`.

## Main results

* `AddCommGrpCat.exists_map_eq_zero_of_isColimit`.
* `Stacks.EtaleCohomology.ScalarExtensionColimit.exists_fg_restriction_eq_zero`: the elementwise
  form of Tag 03Q6 for the scalar extension `X_{k'} ⟶ X`, from the statement of Tag 03Q6 for a
  directed system of algebras (carried as the hypothesis `H03Q6`, in the shape of the registered
  statement; the local definitions `sheafHRestriction`, `algebraCohomologyDiagram` and
  `algebraCohomologyCocone` follow its interface, and are to be replaced by the registered ones).

## Implementation notes

Every comparison map between cohomology groups used here is an `Ext` class pushed along an exact
inverse-image functor and conjugated by isomorphisms (`Stacks.Homology.extConj`). Such a map sends
a class to zero exactly when the pushed class is zero, so the proof only tracks the predicate
"`x` pushed along the inverse image of `φ` is zero", which is stable under precomposing `φ` and
independent of the choice of the isomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AddCommGrpCat

/-- **An element of a stage of a filtered colimit of abelian groups with image zero in the
colimit vanishes at a later stage.** The index is a small category in the universe `u` and the
groups are in `u + 1`, the universes of the cohomology of the schemes of `Scheme.{u}`. -/
theorem exists_map_eq_zero_of_isColimit {K : Type u} [SmallCategory K] [IsFiltered K]
    {F : K ⥤ AddCommGrpCat.{u + 1}} {c : Cocone F} (hc : IsColimit c) {k : K} (y : F.obj k)
    (hy : c.ι.app k y = 0) : ∃ (l : K) (f : k ⟶ l), F.map f y = 0 := by
  have : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} (forget AddCommGrpCat.{u + 1})
  have h0 : c.ι.app k y = c.ι.app k 0 := by rw [hy, map_zero]
  obtain ⟨l, f, g, hfg⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff (F ⋙ forget AddCommGrpCat.{u + 1})
      (isColimitOfPreserves (forget AddCommGrpCat.{u + 1}) hc)
      (xi := y) (xj := (0 : F.obj k))).mp h0
  exact ⟨l, f, by simpa using hfg⟩

end AddCommGrpCat

namespace Stacks.EtaleCohomology.ScalarExtensionColimit

open _root_.AlgebraicGeometry Stacks.Homology Stacks.EtaleCohomology.ColimitBaseChange

/-- `Ext` of abelian sheaves on Mathlib's small étale site at the object universe. -/
local instance (priority := high) hasExt_smallEtale (X : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  have : IsGrothendieckAbelian.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse X
  CategoryTheory.IsGrothendieckAbelian.hasExt _

/-- A class conjugated by two isomorphisms is zero exactly when the class is. -/
theorem extConj_eq_zero_iff {C : Type*} [Category* C] [Abelian C] [HasExt.{u + 1} C]
    {X' X Y Y' : C} (a : X' ⟶ X) (b : Y ⟶ Y') [IsIso a] [IsIso b] {n : ℕ}
    (y : Abelian.Ext.{u + 1} X Y n) : extConj a b y = 0 ↔ y = 0 := by
  have h0 : ∀ {P Q P' Q' : C} (a' : P' ⟶ P) (b' : Q ⟶ Q'),
      extConj a' b' (0 : Abelian.Ext.{u + 1} P Q n) = 0 :=
    fun a' b' => (extConjHom a' b' n).map_zero
  refine ⟨fun h => ?_, fun h => h ▸ h0 a b⟩
  have : extConj (inv a) (inv b) (extConj a b y) = y := by
    rw [extConj_extConj, IsIso.inv_hom_id, IsIso.hom_inv_id, extConj_id]
  rw [← this, h, h0]

variable {X Y Z : Scheme.{u}}

/-- The two inverse images of abelian sheaves agree: both are left adjoint to the direct image. -/
def pullbackAbIso (f : X ⟶ Y) :
    smallEtalePullbackAb f ≅ etaleAbelianInverseImage.{u, u + 1} f :=
  (smallEtaleAdjunctionAb f).leftAdjointUniq (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} f)

section Vanishing

variable {G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} {n : ℕ}

/-- Pushing along a composite: zero exactly when pushing twice is. -/
theorem mapExactFunctor_comp_eq_zero_iff (g : Z ⟶ Y) (φ : Y ⟶ X) (gφ : Z ⟶ X) (h : gφ = g ≫ φ)
    (x : Sheaf.H.{u + 1, u + 1} G n) :
    (x.mapExactFunctor (smallEtalePullbackAb gφ) : Abelian.Ext.{u + 1} _ _ n) = 0 ↔
      ((x.mapExactFunctor (smallEtalePullbackAb φ) : Abelian.Ext.{u + 1} _ _ n).mapExactFunctor
        (smallEtalePullbackAb g) : Abelian.Ext.{u + 1} _ _ n) = 0 := by
  rw [ext_mapExactFunctor_of_iso' _ _ (smallEtalePullbackAbCompIso' g φ gφ h) x,
    extConj_eq_zero_iff, ext_mapExactFunctor_comp_functor]

/-- A class that dies along `φ` dies along every `g ≫ φ`. -/
theorem mapExactFunctor_comp_eq_zero (g : Z ⟶ Y) (φ : Y ⟶ X) (x : Sheaf.H.{u + 1, u + 1} G n)
    (hx : (x.mapExactFunctor (smallEtalePullbackAb φ) : Abelian.Ext.{u + 1} _ _ n) = 0) :
    (x.mapExactFunctor (smallEtalePullbackAb (g ≫ φ)) : Abelian.Ext.{u + 1} _ _ n) = 0 := by
  rw [mapExactFunctor_comp_eq_zero_iff g φ _ rfl, hx]
  exact ((smallEtalePullbackAb g).mapExtAddHom _ _ n).map_zero

/-- Dying along `e.hom ≫ φ` for an isomorphism `e` is dying along `φ`. -/
theorem mapExactFunctor_iso_comp_eq_zero_iff (e : Z ≅ Y) (φ : Y ⟶ X)
    (x : Sheaf.H.{u + 1, u + 1} G n) :
    (x.mapExactFunctor (smallEtalePullbackAb (e.hom ≫ φ)) : Abelian.Ext.{u + 1} _ _ n) = 0 ↔
      (x.mapExactFunctor (smallEtalePullbackAb φ) : Abelian.Ext.{u + 1} _ _ n) = 0 := by
  refine ⟨fun h => ?_, mapExactFunctor_comp_eq_zero e.hom φ x⟩
  have := mapExactFunctor_comp_eq_zero e.inv _ x h
  rwa [Iso.inv_hom_id_assoc] at this

/-- `sheafHRestriction` through an isomorphism kills exactly the classes dying along `φ`. -/
theorem sheafHRestriction_eq_zero_iff (φ : Y ⟶ X)
    {H : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (e : (smallEtalePullbackAb φ).obj G ⟶ H) [IsIso e] (x : Sheaf.H.{u + 1, u + 1} G n) :
    sheafHRestriction φ e n x = 0 ↔
      (x.mapExactFunctor (smallEtalePullbackAb φ) : Abelian.Ext.{u + 1} _ _ n) = 0 := by
  rw [sheafHRestriction_apply, extConj_eq_zero_iff]

/-- Two `sheafHRestriction`s in a row kill exactly the classes dying along the composite. -/
theorem sheafHRestriction_sheafHRestriction_eq_zero_iff (g : Z ⟶ Y) (φ : Y ⟶ X) (gφ : Z ⟶ X)
    (h : gφ = g ≫ φ) {H : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {H' : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (e : (smallEtalePullbackAb φ).obj G ⟶ H) [IsIso e] (e' : (smallEtalePullbackAb g).obj H ⟶ H')
    [IsIso e'] (x : Sheaf.H.{u + 1, u + 1} G n) :
    sheafHRestriction g e' n (sheafHRestriction φ e n x) = 0 ↔
      (x.mapExactFunctor (smallEtalePullbackAb gφ) : Abelian.Ext.{u + 1} _ _ n) = 0 := by
  rw [sheafHRestriction_eq_zero_iff, sheafHRestriction_apply, extConj_mapExactFunctor,
    extConj_eq_zero_iff, mapExactFunctor_comp_eq_zero_iff g φ gφ h]

/-- The restriction map of the library kills exactly the classes dying along `φ`. -/
theorem etaleCohomologyRestrictionMap_eq_zero_iff (φ : Y ⟶ X) (x : Sheaf.H.{u + 1, u + 1} G n) :
    etaleCohomologyRestrictionMap.{u, u + 1, u + 1} φ G n x = 0 ↔
      (x.mapExactFunctor (smallEtalePullbackAb φ) : Abelian.Ext.{u + 1} _ _ n) = 0 := by
  have e1 : etaleCohomologyRestrictionMap.{u, u + 1, u + 1} φ G n x =
      extConj ((etaleAbelianInverseImageConstantIso.{u, u + 1} φ).app
        (AddCommGrpCat.of (ULift ℤ))).inv (𝟙 _)
        (x.mapExactFunctor (etaleAbelianInverseImage.{u, u + 1} φ)) := by
    rw [etaleCohomologyRestrictionMap_apply, extConj, Abelian.Ext.comp_mk₀_id]
  rw [e1, extConj_eq_zero_iff, ext_mapExactFunctor_of_iso' _ _ (pullbackAbIso φ) x,
    extConj_eq_zero_iff]

/-- The restriction map along `pullback.fst f g` kills exactly the classes dying along
`pullback.snd g f`. -/
private theorem restrictionMap_fst_eq_zero_iff {S : Scheme.{u}} (f : Y ⟶ S) (g : X ⟶ S)
    {G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}} (x : Sheaf.H.{u + 1, u + 1} G n) :
    etaleCohomologyRestrictionMap.{u, u + 1, u + 1} (pullback.fst f g) G n x = 0 ↔
      (x.mapExactFunctor (smallEtalePullbackAb (pullback.snd g f)) :
        Abelian.Ext.{u + 1} _ _ n) = 0 := by
  rw [etaleCohomologyRestrictionMap_eq_zero_iff,
    ← mapExactFunctor_iso_comp_eq_zero_iff (pullbackSymmetry f g), pullbackSymmetry_hom_comp_snd]

end Vanishing

/-- **The elementwise form of Tag 03Q6 for the scalar extension `X_{k'} ⟶ X`.** A class on `X`
that dies on `X_{k'}` already dies on `X_A` for a finitely generated `k`-subalgebra `A` of `k'`.

`k'` is the directed colimit of its finitely generated `k`-subalgebras
(`AlgebraicGeometry.FieldExtensionDescent.isColimitSubalgebraCocone`), so by Tag 03Q6
(`Stacks.EtaleCohomology.ColimitBaseChange.isIso_colimitDesc_algebraCohomologyCocone`) the
cohomology of `X_{k'}` is the filtered colimit of the cohomology of the `X_A`; pull the class to
the stage `A = k` and apply `AddCommGrpCat.exists_map_eq_zero_of_isColimit`. -/
theorem exists_fg_restriction_eq_zero
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f]
    [QuasiSeparated f] (k' : Type u) [Field k'] [Algebra k k']
    [HasExt.{u + 1} (Sheaf (scalarExtension k k' f).smallEtaleTopology AddCommGrpCat.{u + 1})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (x : Sheaf.H.{u + 1} F q)
    (hx : etaleCohomologyRestrictionMap.{u, u + 1, u + 1} (scalarExtensionFst k k' f) F q x = 0) :
    ∃ A : Subalgebra k k', A.FG ∧ etaleCohomologyRestrictionMap.{u, u + 1, u + 1}
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k A)))) F q x = 0 := by
  let E := commAlgCatEquivUnder (CommRingCat.of k)
  let B := FieldExtensionDescent.subalgebraDiagram k k' ⋙ E.functor
  let cB := E.functor.mapCocone (FieldExtensionDescent.subalgebraCocone k k')
  have h03Q6 := isIso_colimitDesc_algebraCohomologyCocone (CommRingCat.of k) B cB f F
    (isColimitOfPreserves E.functor (FieldExtensionDescent.isColimitSubalgebraCocone k k')) q
  have hcol : IsColimit (algebraCohomologyCocone (CommRingCat.of k) B cB f F q) :=
    IsColimit.ofPointIso (colimit.isColimit _) (i := h03Q6)
  let i₀ : FieldExtensionDescent.FGSubalgebra k k' := ⟨⊥, Subalgebra.fg_bot⟩
  let y : Sheaf.H.{u + 1, u + 1} (algebraLevelSheaf (CommRingCat.of k) B f F i₀) q :=
    sheafHRestriction (pullback.snd (Spec.map (B.obj i₀).hom) f) (𝟙 _) q x
  have hdie := (restrictionMap_fst_eq_zero_iff f (Spec.map cB.pt.hom) x).mp hx
  have hy : (algebraCohomologyCocone (CommRingCat.of k) B cB f F q).ι.app i₀ y = 0 := by
    rw [algebraCohomologyCocone_ι_app]
    exact (sheafHRestriction_sheafHRestriction_eq_zero_iff (algebraLeg _ B cB f i₀)
      (pullback.snd _ f) (pullback.snd _ f) (algebraLimit_proj _ B cB f (Opposite.op i₀))
      (𝟙 _) _ x).mpr hdie
  obtain ⟨j, g, hg⟩ := AddCommGrpCat.exists_map_eq_zero_of_isColimit hcol y hy
  rw [algebraCohomologyDiagram_map] at hg
  have hj := (sheafHRestriction_sheafHRestriction_eq_zero_iff (algebraTransition _ B f g)
    (pullback.snd _ f) (pullback.snd _ f)
    (levelProj_transition (Spec (CommRingCat.of k)) (Over.mk f) (specDiagram _ B) g.op) (𝟙 _) _
    x).mp hg
  refine ⟨j.1, j.2, ?_⟩
  exact (restrictionMap_fst_eq_zero_iff f _ x).mpr hj

/-- The eight assertions of Situation 0A52 for every torsion sheaf on a separated scheme of
finite type and dimension at most one over an algebraically closed field: Tag 03SC, from Tag 03Q6
through `exists_fg_restriction_eq_zero`. -/
theorem _root_.Stacks.EtaleCohomology.TorsionCurveAssertions.of_colimit
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (hdim : topologicalKrullDim X ≤ 1) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) :
    TorsionCurveAssertions f F :=
  TorsionCurveAssertions.of_inputs
    (fun f _ _ k' _ _ _ F q x hx => exists_fg_restriction_eq_zero f k' F q x hx) f hdim F hF

end Stacks.EtaleCohomology.ScalarExtensionColimit

namespace Stacks.EtaleCohomology

open _root_.AlgebraicGeometry

/-- **Stacks Project, Tag 03SC.** Let `k` be an algebraically closed field, let `X` be a separated
scheme of finite type over `k` of dimension at most one, with structure morphism `f`, and let `F`
be a torsion abelian sheaf on `X_étale`. Then
1. `H^q(X, F) = 0` for `q > 2`;
2. `H^q(X, F) = 0` for `q > 1` if `X` is affine;
3. `H^q(X, F) = 0` for `q > 1` if `char k = p > 0` and `F` is `p`-power torsion;
4. `H^q(X, F)` is finite if `F` is constructible and torsion prime to `char k`;
5. `H^q(X, F)` is finite if `X` is proper and `F` is constructible;
6. `H^q(X, F) → H^q(X_{k'}, F|_{X_{k'}})` is an isomorphism for every extension `k'/k` of
   algebraically closed fields if `F` is torsion prime to `char k`;
7. the same map is an isomorphism if `X` is proper;
8. `H^2(X, F) → H^2(U, F|_U)` is surjective for every open `U ⊂ X`.

These are the fields of `Stacks.EtaleCohomology.TorsionCurveAssertions` (étale cohomology is
`CategoryTheory.Sheaf.H` on Mathlib's small étale site, at coefficients `AddCommGrpCat.{u + 1}`).
"Finite type" is `LocallyOfFiniteType f` together with `QuasiCompact f`; the dimension is the
topological Krull dimension. -/
@[stacks 03SC,
  sga "4 IX 5.7" "special case",
  sga "4 X 5.2" "special case",
  sga "4 XIV 1.2" "special case",
  sga "4½ Arcata 3.3.6",
  sga "5 VI 2.2.1" "special case"]
theorem torsionCurveAssertions {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (hdim : topologicalKrullDim X ≤ 1) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) :
    TorsionCurveAssertions f F :=
  TorsionCurveAssertions.of_colimit f hdim F hF

end Stacks.EtaleCohomology

end
