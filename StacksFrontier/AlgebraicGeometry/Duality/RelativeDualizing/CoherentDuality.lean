module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.CoherentDerivedSubcategory
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.SchemeCoherentDuality
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.CoherentCohomology

/-!
# Duality on the coherent derived category

Let `K` be a dualizing complex on a locally Noetherian scheme `X`. The functor `D = R𝓗om(-, K)`
is an anti-equivalence of `D_Coh(𝒪_X)`, with the biduality morphisms giving `id ≅ D ∘ D`. If `X`
is quasi-compact, `D` exchanges `D^+_Coh(𝒪_X)` and `D^-_Coh(𝒪_X)` and is an anti-equivalence of
`D^b_Coh(𝒪_X)`.

## Main definitions

* `Stacks.Duality.BoundedCoherentDerivedCategory`: the category `D^b_Coh(𝒪_X)`.
* `Stacks.Duality.coherentDuality`: the functor `D` on `D_Coh(𝒪_X)`.
* `Stacks.Duality.coherentBiduality`, `Stacks.Duality.coherentBidualityIso`: the biduality
  morphism and isomorphism `id ⟶ D ∘ D` on `D_Coh(𝒪_X)`.
* `Stacks.Duality.boundedCoherentDuality`: the functor `D` on `D^b_Coh(𝒪_X)`.

## Main results

* `Stacks.Duality.coherentDuality_isEquivalence`: `D` is an anti-equivalence of `D_Coh(𝒪_X)`.
* `Stacks.Duality.isBoundedBelow_iff_isBoundedAbove_derivedSheafHom`: on a quasi-compact `X`,
  `D` exchanges `D^+_Coh(𝒪_X)` and `D^-_Coh(𝒪_X)`.
* `Stacks.Duality.boundedCoherentDuality_isEquivalence`: `D` is an anti-equivalence of
  `D^b_Coh(𝒪_X)`.
* `Stacks.Duality.coherentDuality_spec`: the combined statement.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u w

namespace Stacks.Duality

variable (X : Scheme.{u}) [HasDerivedCategory.{w} X.Modules]

/-- `D^b_Coh(𝒪_X)`: the full subcategory of `D(𝒪_X)` on the bounded objects whose cohomology
sheaves are coherent. -/
abbrev BoundedCoherentDerivedCategory : Type (u + 1) :=
  (DerivedCategoryB.derivedCategoryBBounded (A := X.Modules) (isCoherentSheaf X)).FullSubcategory

variable [IsLocallyNoetherian X]

end Stacks.Duality


/-! ### Duality on `D_Coh(𝒪_X)` -/

namespace Stacks.Duality

section Duality

attribute [local instance 10000] HasDerivedCategory.standard

open Opposite Stacks.SheafOfModules

variable (X : Scheme.{u}) [IsLocallyNoetherian X] {K : DerivedCategory X.Modules}
  (hK : IsDualizingComplex K)

/-- `D = R𝓗om(-, K)` on `D_Coh(𝒪_X)`, for a dualizing complex `K`. -/
def coherentDuality : (CoherentDerivedCategory X)ᵒᵖ ⥤ CoherentDerivedCategory X where
  obj L := ⟨RingedSite.derivedDualInto (Stacks.SheafOfModules.ringedSite X.sheaf) K L.unop.obj,
    isCoherent_homology_derivedSheafHom_of_isDualizingComplex hK L.unop.property⟩
  map f := ObjectProperty.homMk
    (((RingedSite.derivedSheafHomBifunctor (Stacks.SheafOfModules.ringedSite X.sheaf)).map
      f.unop.hom.op).app K)
  map_id L := by
    ext
    exact congrArg (fun φ => NatTrans.app φ K)
      ((RingedSite.derivedSheafHomBifunctor (Stacks.SheafOfModules.ringedSite X.sheaf)).map_id
        (op L.unop.obj))
  map_comp f g := by
    ext
    exact congrArg (fun φ => NatTrans.app φ K)
      ((RingedSite.derivedSheafHomBifunctor (Stacks.SheafOfModules.ringedSite X.sheaf)).map_comp
        f.unop.hom.op g.unop.hom.op)

/-- The canonical morphism `id ⟶ D ∘ D` on `D_Coh(𝒪_X)`, with components the biduality
morphisms `L ⟶ R𝓗om(R𝓗om(L, K), K)`. -/
def coherentBiduality :
    𝟭 (CoherentDerivedCategory X) ⟶
      opOp (CoherentDerivedCategory X) ⋙ (coherentDuality X hK).op ⋙ coherentDuality X hK where
  app L := ObjectProperty.homMk
    (RingedSite.derivedBiduality (Stacks.SheafOfModules.ringedSite X.sheaf) K L.obj)
  naturality L L' f := by
    ext
    simp only [Functor.id_map, Functor.comp_map, Functor.op_map, opOp_map,
      ObjectProperty.FullSubcategory.comp_hom]
    dsimp only [coherentDuality, ObjectProperty.homMk, Quiver.Hom.unop_op]
    exact RingedSite.derivedBiduality_naturality (Stacks.SheafOfModules.ringedSite X.sheaf) K f.hom

example (L : CoherentDerivedCategory X) :
    (L.obj ⟶ RingedSite.derivedDualInto (Stacks.SheafOfModules.ringedSite X.sheaf) K
      (RingedSite.derivedDualInto (Stacks.SheafOfModules.ringedSite X.sheaf) K L.obj)) =
    (L.obj ⟶ ((opOp _ ⋙ (coherentDuality X hK).op ⋙ coherentDuality X hK).obj L).obj) := rfl

example (L : CoherentDerivedCategory X) :
    ((coherentBiduality X hK).app L).hom =
      ((coherentBiduality X hK).app L).hom := rfl

/-- A morphism in a full subcategory is an isomorphism if its underlying morphism is. -/
private theorem isIso_homMk {C : Type*} [Category C] {P : ObjectProperty C}
    {L M : P.FullSubcategory} (f : L.obj ⟶ M.obj) (hf : IsIso f) : IsIso (ObjectProperty.homMk f) :=
  (ObjectProperty.isIso_hom_iff _).1 hf

/-- The biduality morphisms on `D_Coh(𝒪_X)` are isomorphisms. -/
theorem isIso_coherentBiduality : IsIso (coherentBiduality X hK) := by
  have happ : ∀ L, IsIso ((coherentBiduality X hK).app L) := fun L =>
    isIso_homMk _ (isIso_derivedBiduality_of_isDualizingComplex K L.obj hK L.property)
  exact NatIso.isIso_of_isIso_app _

/-- The canonical isomorphism `id ≅ D ∘ D` on `D_Coh(𝒪_X)`. -/
def coherentBidualityIso :
    𝟭 (CoherentDerivedCategory X) ≅
      opOp (CoherentDerivedCategory X) ⋙ (coherentDuality X hK).op ⋙ coherentDuality X hK :=
  have := isIso_coherentBiduality X hK
  asIso (coherentBiduality X hK)

/-- `D` is an anti-equivalence of `D_Coh(𝒪_X)`. -/
theorem coherentDuality_isEquivalence : (coherentDuality X hK).IsEquivalence :=
  Dualizing.isEquivalence_of_opOpNatIso _ (coherentBidualityIso X hK)

/-- The biduality morphism of an object of `D_Coh(𝒪_X)`, as an isomorphism of `D(𝒪_X)`. -/
def derivedBidualityIso (L : DerivedCategory X.Modules)
    (hL : DerivedCategoryB.derivedCategoryB (A := X.Modules) (isCoherentSheaf X) L) :
    L ≅ ((derivedSheafHom X.sheaf).obj (op (((derivedSheafHom X.sheaf).obj (op L)).obj K))).obj K :=
  @asIso (DerivedCategory X.Modules) _ _ _
    (RingedSite.derivedBiduality (Stacks.SheafOfModules.ringedSite X.sheaf) K L)
    (isIso_derivedBiduality_of_isDualizingComplex K L hK hL)

include hK in
/-- On a quasi-compact `X`, duality exchanges `D^+_Coh` and `D^-_Coh`: for `L` in
`D_Coh(𝒪_X)`, `L` is bounded below exactly when `D(L)` is bounded above, and bounded above exactly
when `D(L)` is bounded below. -/
theorem isBoundedBelow_iff_isBoundedAbove_derivedSheafHom [CompactSpace X]
    (L : DerivedCategory X.Modules)
    (hL : DerivedCategoryB.derivedCategoryB (A := X.Modules) (isCoherentSheaf X) L) :
    (DerivedCategoryB.IsBoundedBelow L ↔
      DerivedCategoryB.IsBoundedAbove (((derivedSheafHom X.sheaf).obj (op L)).obj K)) ∧
    (DerivedCategoryB.IsBoundedAbove L ↔
      DerivedCategoryB.IsBoundedBelow (((derivedSheafHom X.sheaf).obj (op L)).obj K)) := by
  have hD : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj
      (((derivedSheafHom X.sheaf).obj (op L)).obj K)).IsCoherent := fun i =>
    isCoherent_homology_derivedSheafHom_of_isDualizingComplex hK hL i
  let e := derivedBidualityIso X hK L hL
  refine ⟨⟨isBoundedAbove_derivedSheafHom_of_isDualizingComplex hK hL, fun h => ?_⟩,
    ⟨isBoundedBelow_derivedSheafHom_of_isDualizingComplex hK hL, fun h => ?_⟩⟩
  · obtain ⟨n₀, hn₀⟩ := isBoundedBelow_derivedSheafHom_of_isDualizingComplex hK hD h
    exact ⟨n₀, fun n hn => (hn₀ n hn).of_iso
      ((DerivedCategory.homologyFunctor X.Modules n).mapIso e)⟩
  · obtain ⟨n₀, hn₀⟩ := isBoundedAbove_derivedSheafHom_of_isDualizingComplex hK hD h
    exact ⟨n₀, fun n hn => (hn₀ n hn).of_iso
      ((DerivedCategory.homologyFunctor X.Modules n).mapIso e)⟩

include hK in
/-- On a quasi-compact `X`, duality preserves `D^b_Coh(𝒪_X)`. -/
theorem derivedCategoryBBounded_derivedSheafHom [CompactSpace X] (L : DerivedCategory X.Modules)
    (hL : DerivedCategoryB.derivedCategoryBBounded (A := X.Modules) (isCoherentSheaf X) L) :
    DerivedCategoryB.derivedCategoryBBounded (A := X.Modules) (isCoherentSheaf X)
      (((derivedSheafHom X.sheaf).obj (op L)).obj K) :=
  ⟨⟨isBoundedBelow_derivedSheafHom_of_isDualizingComplex hK hL.2 hL.1.2,
    isBoundedAbove_derivedSheafHom_of_isDualizingComplex hK hL.2 hL.1.1⟩,
    fun i => isCoherent_homology_derivedSheafHom_of_isDualizingComplex hK hL.2 i⟩

include hK in
/-- `D = R𝓗om(-, K)` on `D^b_Coh(𝒪_X)`, for `X` quasi-compact. -/
def boundedCoherentDuality [CompactSpace X] :
    (BoundedCoherentDerivedCategory X)ᵒᵖ ⥤ BoundedCoherentDerivedCategory X where
  obj L := ⟨RingedSite.derivedDualInto (Stacks.SheafOfModules.ringedSite X.sheaf) K L.unop.obj,
    derivedCategoryBBounded_derivedSheafHom X hK L.unop.obj L.unop.property⟩
  map f := ObjectProperty.homMk
    (((RingedSite.derivedSheafHomBifunctor (Stacks.SheafOfModules.ringedSite X.sheaf)).map
      f.unop.hom.op).app K)
  map_id L := by
    ext
    exact congrArg (fun φ => NatTrans.app φ K)
      ((RingedSite.derivedSheafHomBifunctor (Stacks.SheafOfModules.ringedSite X.sheaf)).map_id
        (op L.unop.obj))
  map_comp f g := by
    ext
    exact congrArg (fun φ => NatTrans.app φ K)
      ((RingedSite.derivedSheafHomBifunctor (Stacks.SheafOfModules.ringedSite X.sheaf)).map_comp
        f.unop.hom.op g.unop.hom.op)

/-- The canonical morphism `id ⟶ D ∘ D` on `D^b_Coh(𝒪_X)`. -/
def boundedCoherentBiduality [CompactSpace X] :
    𝟭 (BoundedCoherentDerivedCategory X) ⟶
      opOp (BoundedCoherentDerivedCategory X) ⋙ (boundedCoherentDuality X hK).op ⋙
        boundedCoherentDuality X hK where
  app L := ObjectProperty.homMk
    (RingedSite.derivedBiduality (Stacks.SheafOfModules.ringedSite X.sheaf) K L.obj)
  naturality L L' f := by
    ext
    simp only [Functor.id_map, Functor.comp_map, Functor.op_map, opOp_map,
      ObjectProperty.FullSubcategory.comp_hom]
    dsimp only [coherentDuality, ObjectProperty.homMk, Quiver.Hom.unop_op]
    exact RingedSite.derivedBiduality_naturality (Stacks.SheafOfModules.ringedSite X.sheaf) K f.hom

/-- The biduality morphisms on `D^b_Coh(𝒪_X)` are isomorphisms. -/
theorem isIso_boundedCoherentBiduality [CompactSpace X] :
    IsIso (boundedCoherentBiduality X hK) := by
  have happ : ∀ L, IsIso ((boundedCoherentBiduality X hK).app L) := fun L =>
    isIso_homMk _ (isIso_derivedBiduality_of_isDualizingComplex K L.obj hK L.property.2)
  exact NatIso.isIso_of_isIso_app _

/-- `D` is an anti-equivalence of `D^b_Coh(𝒪_X)`, for `X` quasi-compact. -/
theorem boundedCoherentDuality_isEquivalence [CompactSpace X] :
    (boundedCoherentDuality X hK).IsEquivalence :=
  have := isIso_boundedCoherentBiduality X hK
  Dualizing.isEquivalence_of_opOpNatIso _ (asIso (boundedCoherentBiduality X hK))

/-- Let `K` be a dualizing complex on a locally Noetherian scheme
`X`. Then `K` is an object of `D_Coh(𝒪_X)`, and `D = R𝓗om(-, K)` carries `D_Coh(𝒪_X)` into itself
and induces an anti-equivalence `D : D_Coh(𝒪_X) → D_Coh(𝒪_X)` which comes with the canonical
isomorphism `id → D ∘ D`, the biduality morphisms `L → R𝓗om(R𝓗om(L, K), K)`. If `X` is
quasi-compact, `D` exchanges `D^+_Coh(𝒪_X)` and `D^-_Coh(𝒪_X)` and induces an anti-equivalence
`D^b_Coh(𝒪_X) → D^b_Coh(𝒪_X)`. -/
@[stacks 0A89]
theorem coherentDuality_spec :
    DerivedCategoryB.derivedCategoryB (A := X.Modules) (isCoherentSheaf X) K ∧
    (∀ L : DerivedCategory X.Modules,
      DerivedCategoryB.derivedCategoryB (A := X.Modules) (isCoherentSheaf X) L →
      DerivedCategoryB.derivedCategoryB (A := X.Modules) (isCoherentSheaf X)
        (((derivedSheafHom X.sheaf).obj (op L)).obj K)) ∧
    (coherentDuality X hK).IsEquivalence ∧
    IsIso (coherentBiduality X hK) ∧
    (∀ [CompactSpace X],
      (∀ L : DerivedCategory X.Modules,
        DerivedCategoryB.derivedCategoryB (A := X.Modules) (isCoherentSheaf X) L →
        (DerivedCategoryB.IsBoundedBelow L ↔
          DerivedCategoryB.IsBoundedAbove (((derivedSheafHom X.sheaf).obj (op L)).obj K)) ∧
        (DerivedCategoryB.IsBoundedAbove L ↔
          DerivedCategoryB.IsBoundedBelow (((derivedSheafHom X.sheaf).obj (op L)).obj K))) ∧
      (boundedCoherentDuality X hK).IsEquivalence) :=
  ⟨mem_coherentDerivedCategory_of_isDualizingComplex X hK,
    fun _ hL i => isCoherent_homology_derivedSheafHom_of_isDualizingComplex hK hL i,
    coherentDuality_isEquivalence X hK, isIso_coherentBiduality X hK,
    fun [CompactSpace X] =>
      ⟨fun L hL => isBoundedBelow_iff_isBoundedAbove_derivedSheafHom X hK L hL,
        boundedCoherentDuality_isEquivalence X hK⟩⟩

end Duality

end Stacks.Duality

end
