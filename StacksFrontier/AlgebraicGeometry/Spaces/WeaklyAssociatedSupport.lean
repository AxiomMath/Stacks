module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Zero
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPoints

/-!
# Weakly associated points lie in the support

Let `X` be an algebraic space over `S` and `F` an `𝒪_X`-module. Every weakly associated point
of `F` lies in the support of the abelian sheaf underlying `F`: at a weakly associated point
the maximal ideal of the étale local ring is a weakly associated prime of the geometric stalk,
so that stalk is nonzero.

## Main results

* `AlgebraicGeometry.Space.weaklyAssociatedPoints_subset_supportOfSheaf` is the inclusion
  `WeakAss(F) ⊆ Supp(F)`.

## Implementation notes

The support of Stacks 04KA is formed from the set-valued stalk of the abelian sheaf
`AlgebraicGeometry.SheafOfModules.toSheaf.obj F`, whereas weak association is formulated
through `AlgebraicGeometry.Space.geometricModuleStalk`, the stalk at the point of the small
étale site with its scalars extended to the étale local ring. The comparison of the two is the
content of the proof: the set-valued stalk is a quotient colimit indexed by the small étale
neighbourhoods, while the module stalk is a colimit of lifted sections indexed by a small final
model of the elements of the geometric fibre, and extension of scalars along a ring isomorphism
does not create elements.

The inclusion holds for every `𝒪_X`-module, quasi-coherent or not, since neither of the two
conditions involved uses quasi-coherence.

## References

* [Stacks Project, Lemma 71.2.3 (Tag 0CTY)](https://stacks.math.columbia.edu/tag/0CTY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] FinallySmall.preservesColimitsOfShape_of_isFiltered

universe u m

namespace AlgebraicGeometry.Space

/-- A module with a weakly associated prime is nonzero: the annihilator of the element
witnessing the weak association is not the whole ring. -/
private theorem weaklyAssociatedPrime_nontrivial
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {I : Ideal R} (h : IsWeaklyAssociatedPrime R M I) : Nontrivial M := by
  by_contra hn
  let _ : Subsingleton M := not_nontrivial_iff_subsingleton.mp hn
  obtain ⟨m, hm⟩ := h
  have : (R ∙ m).annihilator = ⊤ := by simp [Subsingleton.elim m 0, Submodule.annihilator]
  exact hm.1.1.ne_top (top_le_iff.mp (this ▸ hm.1.2))

/-- The colimit of a presheaf of sets over the elements of the geometric fibre is the
set-valued stalk at the geometric point, with the universe of the values unconstrained. -/
private noncomputable def fiberColimitEquivLarge
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (x : GeometricPoint B S hS F) (P : (SmallEtale B S hS F)ᵒᵖ ⥤ Type m) :
    ((Functor.Elements.π (geometricFiber B S hS F x)).op ⋙ P).ColimitType ≃
      stalkSet x P where
  toFun := Quot.map
    (fun a => ⟨Opposite.op ((fiberElementsToNeighborhood B S hS F x).obj a.1.unop), a.2⟩)
    (by
      rintro ⟨j, a⟩ ⟨k, b⟩ ⟨f, h⟩
      exact ⟨((fiberElementsToNeighborhood B S hS F x).map f.unop).op, h⟩)
  invFun := Quot.map
    (fun a => ⟨Opposite.op ((neighborhoodToFiberElements B S hS F x).obj a.1.unop), a.2⟩)
    (by
      rintro ⟨j, a⟩ ⟨k, b⟩ ⟨f, h⟩
      exact ⟨((neighborhoodToFiberElements B S hS F x).map f.unop).op, h⟩)
  left_inv a := by induction a using Quot.inductionOn; rfl
  right_inv a := by induction a using Quot.inductionOn; rfl

/-- Lifting the sections of a presheaf of abelian groups to a larger universe does not change
the set-valued stalk at a geometric point. -/
private noncomputable def stalkSetAddCommGrpUliftEquiv
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (x : GeometricPoint B S hS X) (P : (SmallEtale B S hS X)ᵒᵖ ⥤ AddCommGrpCat.{m}) :
    stalkSet x (P ⋙ AddCommGrpCat.uliftFunctor.{u} ⋙ forget AddCommGrpCat) ≃
      stalkSet x (P ⋙ forget AddCommGrpCat.{m}) where
  toFun := Quot.map (fun a => by
      dsimp [SmallEtaleNeighborhood.sections, AddCommGrpCat.uliftFunctor] at a ⊢
      exact ⟨a.1, a.2.down⟩)
    (by
      rintro ⟨j, a⟩ ⟨k, b⟩ ⟨f, h⟩
      exact ⟨f, congrArg ULift.down h⟩)
  invFun := Quot.map (fun a => by
      dsimp [SmallEtaleNeighborhood.sections, AddCommGrpCat.uliftFunctor] at a ⊢
      exact ⟨a.1, ULift.up.{u, m} a.2⟩)
    (by
      rintro ⟨j, a⟩ ⟨k, b⟩ ⟨f, h⟩
      exact ⟨f, congrArg ULift.up h⟩)
  left_inv a := by induction a using Quot.inductionOn; rfl
  right_inv a := by induction a using Quot.inductionOn; rfl

/-- If the set-valued stalk of the abelian sheaf underlying an `𝒪_X`-module is a subsingleton
at a geometric point, then so is the stalk of the module at the corresponding point of the
small étale site. -/
private theorem moduleStalkLarge_subsingleton_of_stalkSet
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (x : GeometricPoint B S hS X.1)
    (F : Modules.{u, m} B S hS X.1 X.2)
    (h : Subsingleton
      (stalkSet x (((SheafOfModules.toSheaf _).obj F).obj ⋙ forget AddCommGrpCat.{m}))) :
    Subsingleton (Stacks.moduleStalkLarge (etaleSitePoint B S hS X.1 x X.2)
      (smallEtaleRingedTopos B S hS X).O F) := by
  classical
  let p := etaleSitePoint B S hS X.1 x X.2
  have hp : p.fiber = geometricFiber B S hS X.1 x := etaleSitePoint_fiber B S hS X.1 x X.2
  let D := FinallySmall.FilteredFinalModel.{u} (p.fiber.Elementsᵒᵖ)
  let J : D ⥤ p.fiber.Elementsᵒᵖ := FinallySmall.fromFilteredFinalModel _
  let P0 := F.val.presheaf
  let P := P0 ⋙ AddCommGrpCat.uliftFunctor.{u} ⋙ forget AddCommGrpCat
  let G := (Functor.Elements.π p.fiber).op ⋙ P0 ⋙ AddCommGrpCat.uliftFunctor.{u}
  let GType := (Functor.Elements.π p.fiber).op ⋙ P
  let _ : HasColimit G := Functor.Final.hasColimit_of_comp J
  have hStalk : Subsingleton (stalkSet x P) :=
    (stalkSetAddCommGrpUliftEquiv x P0).subsingleton_congr.mpr h
  let e : GType.ColimitType ≃ stalkSet x P := by
    change ((Functor.Elements.π p.fiber).op ⋙ P).ColimitType ≃ _
    rw [hp]
    exact fiberColimitEquivLarge (B := B) (S := S) (hS := hS) (F := X.1) x P
  let cG := colimit.cocone G
  have hι (j : p.fiber.Elementsᵒᵖ) (a : G.obj j) : cG.ι.app j a = 0 := by
    have hq : GType.ιColimitType j a = GType.ιColimitType j (0 : G.obj j) :=
      e.injective (Subsingleton.elim _ _)
    obtain ⟨k, f, g, hfg⟩ :=
      (Functor.ιColimitType_eq_iff_of_isFiltered (F := GType) a (0 : G.obj j)).mp hq
    calc
      cG.ι.app j a = cG.ι.app k (G.map f a) := by simp
      _ = cG.ι.app k (G.map g (0 : G.obj j)) := congrArg _ hfg
      _ = 0 := by simp
  have hId : (𝟙 cG.pt : cG.pt ⟶ cG.pt) = 0 :=
    colimit.hom_ext (F := G) fun j => by
      ext a
      exact hι j a
  exact
    ((forget AddCommGrpCat).mapIso (Functor.Final.colimitIso J G)).toEquiv.subsingleton_congr.mpr
      (AddCommGrpCat.subsingleton_of_isZero ((IsZero.iff_id_eq_zero cG.pt).mpr hId))

/-- **Stacks 0CTY.** The weakly associated points of an `𝒪_X`-module on an algebraic space lie
in the support of its underlying abelian sheaf. -/
@[stacks 0CTY]
theorem weaklyAssociatedPoints_subset_supportOfSheaf
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (F : Modules.{u, m} B S hS X.1 X.2) :
    weaklyAssociatedPoints B S hS X F ⊆
      supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) := by
  intro x hx
  rw [mem_supportOfSheaf_iff_exists]
  obtain ⟨xbar, hxbar, hwa⟩ := (mem_weaklyAssociatedPoints_iff B S hS X F x).mp hx
  refine ⟨xbar, hxbar, ?_⟩
  intro hsub
  have := moduleStalkLarge_subsingleton_of_stalkSet B S hS X xbar F hsub
  have : Subsingleton (geometricModuleStalk B S hS X xbar F) := by
    dsimp [geometricModuleStalk, ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj']
    infer_instance
  exact (not_nontrivial_iff_subsingleton.mpr inferInstance)
    (weaklyAssociatedPrime_nontrivial hwa)

end AlgebraicGeometry.Space

end
