module

public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.AdamsOperator.SupportedCoherent
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Support
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksCore.CategoryTheory.Abelian.SerreClass.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Coherent modules whose support has bounded delta-dimension

Let `X` be a scheme locally of finite type over the base scheme of chapter 42 of the Stacks
Project. The delta-dimension of the support of a coherent `𝒪_X`-module `F` is the
delta-dimension of the reduced closed subscheme `Stacks.Chow.reducedSupport F`, and it is at
most `k` exactly when every point of the support has relative dimension at most `k`. Coherent
modules with support of delta-dimension at most `k` form a Serre subcategory of the category of
coherent modules.

## Main definitions

* `Stacks.Chow.coherentModulesDimLE` — the property of a coherent module that the
  delta-dimension of its support is at most `k`.
* `Stacks.Chow.CoherentModulesDimLE` — the corresponding full subcategory of coherent modules.

## Main results

* `Stacks.Chow.schemeDeltaDimension_reducedSupport_le_iff` — the bound on the delta-dimension of
  the support is the pointwise bound on the relative dimension along the support.
* `Stacks.Chow.coherentModulesDimLE_isSerreClass` — Stacks 02S8, the Serre property.

## Implementation notes

The three closure conditions are not checked on stalks again. The union of the supports of two
coherent modules is closed, hence the underlying set of a reduced closed subscheme, and
`AlgebraicGeometry.supportedCoherentIsSerreClass` already says that coherent modules supported
on a closed subscheme form a Serre class; its middle-term condition is exactly the statement
that the support of the middle term of an exact short complex lies in the union of the supports
of the outer terms. Taking the empty closed subscheme gives in the same way a coherent module
whose support is empty, which is the nonemptiness half of Stacks 02MP.

## References

* [Stacks Project, Tag 02MP](https://stacks.math.columbia.edu/tag/02MP)
* [Stacks Project, Tag 02QP](https://stacks.math.columbia.edu/tag/02QP)
* [Stacks Project, Tag 02S8](https://stacks.math.columbia.edu/tag/02S8)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}}

/-! ### The dimension bound as a condition on the support -/

/-- The reduced closed subscheme carried by the support of a coherent module has that support as
its range. -/
private theorem range_subschemeι_reducedSupport (F : X.Modules) [F.IsCoherent] :
    Set.range (reducedSupport F).subschemeι.base = SheafOfModules.supp F := by
  rw [Scheme.IdealSheafData.range_subschemeι, coe_support_reducedSupport]

/-- If the support of a coherent module has delta-dimension at most `k`, then every point of the
support has relative dimension at most `k`. -/
theorem relativeDimension_le_of_mem_supp (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsCoherent] {k : ℤ}
    (hF : schemeDeltaDimension C ((reducedSupport F).subschemeι ≫ f) ≤ (k : EInt)) {x : X}
    (hx : x ∈ SheafOfModules.supp F) :
    relativeDimension C.dimensionFunction f x ≤ k := by
  obtain ⟨z, rfl⟩ : x ∈ Set.range (reducedSupport F).subschemeι.base := by
    rwa [range_subschemeι_reducedSupport]
  exact relativeDimension_le_of_schemeDeltaDimension_le C f _ hF z

/-- If every point of the support of a coherent module has relative dimension at most `k`, then
the support has delta-dimension at most `k`. -/
theorem schemeDeltaDimension_reducedSupport_le (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsCoherent] {k : ℤ}
    (hF : ∀ x ∈ SheafOfModules.supp F, relativeDimension C.dimensionFunction f x ≤ k) :
    schemeDeltaDimension C ((reducedSupport F).subschemeι ≫ f) ≤ (k : EInt) := by
  refine iSup_le fun W => WithBotTop.coe_le_coe.mpr ?_
  set i := (reducedSupport F).subschemeι with hi
  have hgen : IsGenericPoint W.2.1.genericPoint (W : Set (reducedSupport F).subscheme) :=
    W.2.1.isGenericPoint_genericPoint
      (isClosed_of_mem_irreducibleComponents (W : Set (reducedSupport F).subscheme) W.2)
  rw [deltaDimension_eq_of_isGenericPoint C (i ≫ f) _ _ hgen,
    relativeDimension_comp_closedImmersion C.dimensionFunction i f]
  exact hF _ (by rw [← range_subschemeι_reducedSupport F]; exact ⟨_, rfl⟩)

/-- The support of a coherent module has delta-dimension at most `k` exactly when every point of
the support has relative dimension at most `k`. -/
theorem schemeDeltaDimension_reducedSupport_le_iff (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsCoherent] (k : ℤ) :
    schemeDeltaDimension C ((reducedSupport F).subschemeι ≫ f) ≤ (k : EInt) ↔
      ∀ x ∈ SheafOfModules.supp F, relativeDimension C.dimensionFunction f x ≤ k :=
  ⟨fun hF _ hx => relativeDimension_le_of_mem_supp C f F hF hx,
    schemeDeltaDimension_reducedSupport_le C f F⟩

/-! ### Supports of exact short complexes of coherent modules -/

/-- The reduced closed subscheme of `X` carried by a closed subset. -/
private noncomputable def reducedClosed (T : Set X) (hT : IsClosed T) : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨T, hT⟩

/-- The reduced closed subscheme carried by a closed subset has that subset as its range. -/
private theorem range_subschemeι_reducedClosed (T : Set X) (hT : IsClosed T) :
    Set.range (reducedClosed T hT).subschemeι.base = T := by
  rw [Scheme.IdealSheafData.range_subschemeι, reducedClosed,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

/-- There is a coherent module whose support is contained in any given subset. -/
private theorem exists_supp_subset [IsLocallyNoetherian X] (T : Set X) :
    ∃ F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf,
      SheafOfModules.supp F.obj ⊆ T := by
  obtain ⟨Z, -, hZ⟩ := ObjectProperty.exists_prop_of_containsZero
    (supportedCoherentProperty (reducedClosed (∅ : Set X) isClosed_empty).subschemeι)
  exact ⟨Z, (hZ.trans (range_subschemeι_reducedClosed (∅ : Set X) isClosed_empty).subset).trans
    (Set.empty_subset T)⟩

/-- The support of the middle term of an exact short complex of coherent modules is contained in
the union of the supports of the outer terms. -/
private theorem supp_subset_union_supp_of_exact [IsLocallyNoetherian X]
    (S : ShortComplex (Stacks.SheafOfModules.CoherentModules X.ringCatSheaf)) (hS : S.Exact) :
    SheafOfModules.supp S.X₂.obj ⊆
      SheafOfModules.supp S.X₁.obj ∪ SheafOfModules.supp S.X₃.obj := by
  set T := SheafOfModules.supp S.X₁.obj ∪ SheafOfModules.supp S.X₃.obj with hT
  have hcl : IsClosed T :=
    (SheafOfModules.isClosed_supp S.X₁.obj).union (SheafOfModules.isClosed_supp S.X₃.obj)
  have hrange := range_subschemeι_reducedClosed T hcl
  have key := ((ObjectProperty.isSerreClass_iff_prop_X₂_of_exact
    (supportedCoherentProperty (reducedClosed T hcl).subschemeι)).1 inferInstance).2 S hS
  have h₁ : SheafOfModules.supp S.X₁.obj ⊆
      Set.range (reducedClosed T hcl).subschemeι.base := by
    rw [hrange, hT]; exact Set.subset_union_left
  have h₃ : SheafOfModules.supp S.X₃.obj ⊆
      Set.range (reducedClosed T hcl).subschemeι.base := by
    rw [hrange, hT]; exact Set.subset_union_right
  rw [← hrange]
  exact key h₁ h₃

/-! ### The Serre subcategory of modules of bounded support dimension -/

/-- The property of a coherent `𝒪_X`-module that the delta-dimension of its support is at most
`k`, for `X` locally of finite type over the base scheme of chapter 42. -/
noncomputable abbrev coherentModulesDimLE (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) :
    ObjectProperty (Stacks.SheafOfModules.CoherentModules X.ringCatSheaf) :=
  fun F =>
    haveI : _root_.SheafOfModules.IsCoherent F.obj :=
      AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent F.property
    schemeDeltaDimension C ((reducedSupport F.obj).subschemeι ≫ f) ≤ (k : EInt)

/-- The full subcategory of coherent `𝒪_X`-modules whose support has delta-dimension at most
`k`. -/
noncomputable abbrev CoherentModulesDimLE (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) :=
  (coherentModulesDimLE C f k).FullSubcategory

/-- **Stacks 02S8.** Coherent `𝒪_X`-modules whose support has delta-dimension at most `k` form a
Serre subcategory of the category of coherent `𝒪_X`-modules. -/
@[stacks 02S8]
noncomputable instance coherentModulesDimLE_isSerreClass (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) : (coherentModulesDimLE C f k).IsSerreClass := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  set T : Set X := {x | relativeDimension C.dimensionFunction f x ≤ k} with hT
  have hiff : ∀ F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf,
      coherentModulesDimLE C f k F ↔ SheafOfModules.supp F.obj ⊆ T := fun F =>
    haveI : _root_.SheafOfModules.IsCoherent F.obj :=
      AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent F.property
    schemeDeltaDimension_reducedSupport_le_iff C f F.obj k
  refine (ObjectProperty.isSerreClass_iff_prop_X₂_of_exact _).2 ⟨?_, fun S hS h₁ h₃ => ?_⟩
  · obtain ⟨F, hF⟩ := exists_supp_subset T
    exact ⟨F, (hiff F).2 hF⟩
  · exact (hiff _).2 (((supp_subset_union_supp_of_exact S hS).trans
      (Set.union_subset ((hiff _).1 h₁) ((hiff _).1 h₃))))

/-- The dimension bound is monotone in `k`. -/
theorem coherentModulesDimLE_le_coherentModulesDimLE (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] {k l : ℤ} (hkl : k ≤ l) :
    coherentModulesDimLE C f k ≤ coherentModulesDimLE C f l :=
  fun _ hF => hF.trans (WithBotTop.coe_le_coe.mpr hkl)

/-- The inclusion of coherent `𝒪_X`-modules with support of delta-dimension at most `k` into all
coherent `𝒪_X`-modules is left exact. -/
noncomputable instance preservesFiniteLimits_ι_coherentModulesDimLE (C : ChowSituation.{u})
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ) :
    PreservesFiniteLimits (coherentModulesDimLE C f k).ι :=
  ObjectProperty.preservesFiniteLimits_ι_of_isWeakSerreClass _

/-- The inclusion of coherent `𝒪_X`-modules with support of delta-dimension at most `k` into all
coherent `𝒪_X`-modules is right exact. -/
noncomputable instance preservesFiniteColimits_ι_coherentModulesDimLE (C : ChowSituation.{u})
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ) :
    PreservesFiniteColimits (coherentModulesDimLE C f k).ι :=
  ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass _

/-- An isomorphism of the underlying `𝒪_X`-modules of two objects of `Coh_{≤k}(X)` lifts to an
isomorphism in `Coh_{≤k}(X)`. -/
public def dimLEIsoOfModuleIso (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) (M M' : CoherentModulesDimLE C f k)
    (e : M.obj.obj ≅ M'.obj.obj) : M ≅ M' :=
  (ObjectProperty.fullyFaithfulι _).preimageIso
    ((ObjectProperty.fullyFaithfulι _).preimageIso e)

end Stacks.Chow
