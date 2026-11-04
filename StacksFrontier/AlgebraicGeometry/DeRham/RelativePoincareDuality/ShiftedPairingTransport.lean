module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.PairingFiveLemma
public import StacksFrontier.CategoryTheory.Shift.CommShiftTwoOfIso
public import StacksFrontier.CategoryTheory.Shift.CommShiftTwoPostcomp
public import StacksFrontier.CategoryTheory.CurryPostcomp

/-!
# Shifted pairings along transformations, restrictions and postcompositions of bifunctors

For a bifunctor `G : C₁ ⥤ C₂ ⥤ D` commuting with the shifts in both variables, the shift
`G.shiftedPairing φ n m h : K[n] ⊗ L[m] ⟶ M` of a pairing `φ : K ⊗ L ⟶ M` (`n + m = 0`) is built
from the commutation isomorphisms of `G`. This file records how it behaves when `G` is changed:

* along a transformation `τ : G₁ ⟶ G₂` compatible with the shifts, the shift of `τ ≫ φ` is
  `τ` followed by the shift of `φ`;
* along a restriction of `G` in the first or second variable by a shift-compatible functor, the
  shift is the commutation isomorphism of that functor followed by the shift for `G`;
* along a postcomposition of `G` with a shift-compatible functor `H`, the shift of `H(ψ)` is
  `H` of the shift of `ψ`.

These are the steps by which the commutation of the canonical map `K ⊗^L L ⟶ Tot(K ⊗ L)` with the
shifts is turned into an equation between shifted pairings, as the proof of
[Stacks, Tag 0G8K] needs.

## Main results

* `CategoryTheory.Functor.shiftedPairing_natTrans`
* `CategoryTheory.Functor.shiftedPairing_precomp₁`
* `CategoryTheory.Functor.shiftedPairing_precomp₂`
* `CategoryTheory.Functor.shiftedPairing_postcompInt`
* `CategoryTheory.Functor.shiftedPairing_curryObjUncurryObjComp`

## References

* [Stacks Project, Tag 0G8K](https://stacks.math.columbia.edu/tag/0G8K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {C₁ C₂ C₁' C₂' D D' : Type*} [Category* C₁] [Category* C₂] [Category* C₁']
  [Category* C₂'] [Category* D] [Category* D']
  [HasShift C₁ ℤ] [HasShift C₂ ℤ] [HasShift C₁' ℤ] [HasShift C₂' ℤ] [HasShift D ℤ]
  [HasShift D' ℤ] [Preadditive D] [Preadditive D'] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D' n).Additive]

/-- **The shift of a pairing along a transformation of bifunctors compatible with the shifts**:
the shift of `τ ≫ φ` is `τ` followed by the shift of `φ`. -/
theorem shiftedPairing_natTrans {G₁ G₂ : C₁ ⥤ C₂ ⥤ D} [G₁.CommShift₂Int] [G₂.CommShift₂Int]
    (τ : G₁ ⟶ G₂) [NatTrans.CommShift₂Int τ] {K : C₁} {L : C₂} {M : D}
    (φ : (G₂.obj K).obj L ⟶ M) (n m : ℤ) (h : n + m = 0) :
    G₁.shiftedPairing ((τ.app K).app L ≫ φ) n m h =
      (τ.app (K⟦n⟧)).app (L⟦m⟧) ≫ G₂.shiftedPairing φ n m h := by
  have h₁ := NatTrans.shift_app_comm (τ.app (K⟦n⟧)) m L
  have h₂ : ((G₁.flip.obj L).commShiftIso n).hom.app K ≫ ((τ.app K).app L)⟦n⟧' =
      (τ.app (K⟦n⟧)).app L ≫ ((G₂.flip.obj L).commShiftIso n).hom.app K :=
    NatTrans.shift_app_comm (τ.flipApp L) n K
  have h₃ := (shiftFunctorCompIsoId D n m h).hom.naturality ((τ.app K).app L)
  simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.id_map] at h₁ h₃
  simp only [shiftedPairing]
  rw [← reassoc_of% h₃, ← Functor.map_comp_assoc, h₂, Functor.map_comp_assoc, reassoc_of% h₁]

/-- **The shift of a pairing along a restriction in the first variable**: for
`F : C₁' ⥤ C₁` compatible with the shifts, the shift for `F ⋙ G` is the commutation isomorphism of
`F` followed by the shift for `G`. -/
theorem shiftedPairing_precomp₁ (F : C₁' ⥤ C₁) [F.CommShift ℤ] (G : C₁ ⥤ C₂ ⥤ D)
    [G.CommShift₂Int] {K : C₁'} {L : C₂} {M : D} (φ : (G.obj (F.obj K)).obj L ⟶ M) (n m : ℤ)
    (h : n + m = 0) :
    (F ⋙ G).shiftedPairing φ n m h =
      (G.map ((F.commShiftIso n).hom.app K)).app (L⟦m⟧) ≫ G.shiftedPairing φ n m h := by
  have e : (((F ⋙ G).flip.obj L).commShiftIso n).hom.app K =
      (G.map ((F.commShiftIso n).hom.app K)).app L ≫
        ((G.flip.obj L).commShiftIso n).hom.app (F.obj K) :=
    Functor.commShiftIso_comp_hom_app F (G.flip.obj L) n K
  have h₁ : (((F ⋙ G).obj (K⟦n⟧)).commShiftIso m).hom.app L ≫
        ((G.map ((F.commShiftIso n).hom.app K)).app L)⟦m⟧' =
      (G.map ((F.commShiftIso n).hom.app K)).app (L⟦m⟧) ≫
        ((G.obj ((F.obj K)⟦n⟧)).commShiftIso m).hom.app L :=
    NatTrans.shift_app_comm (G.map ((F.commShiftIso n).hom.app K)) m L
  simp only [shiftedPairing, e, Functor.map_comp, Category.assoc]
  exact (Category.assoc _ _ _).symm.trans ((h₁ =≫ _).trans (Category.assoc _ _ _))

/-- **The shift of a pairing along a restriction in the second variable**: for
`F : C₂' ⥤ C₂` compatible with the shifts, the shift for the restriction of `G` along `F` in its
second variable is the commutation isomorphism of `F` followed by the shift for `G`. -/
theorem shiftedPairing_precomp₂ (F : C₂' ⥤ C₂) [F.CommShift ℤ] (G : C₁ ⥤ C₂ ⥤ D)
    [G.CommShift₂Int] {K : C₁} {L : C₂'} {M : D} (φ : (G.obj K).obj (F.obj L) ⟶ M) (n m : ℤ)
    (h : n + m = 0) :
    (G ⋙ (whiskeringLeft C₂' C₂ D).obj F).shiftedPairing φ n m h =
      (G.obj (K⟦n⟧)).map ((F.commShiftIso m).hom.app L) ≫ G.shiftedPairing φ n m h := by
  have e : (((G ⋙ (whiskeringLeft C₂' C₂ D).obj F).obj (K⟦n⟧)).commShiftIso m).hom.app L =
      (G.obj (K⟦n⟧)).map ((F.commShiftIso m).hom.app L) ≫
        ((G.obj (K⟦n⟧)).commShiftIso m).hom.app (F.obj L) :=
    Functor.commShiftIso_comp_hom_app F (G.obj (K⟦n⟧)) m L
  simp only [shiftedPairing, e, Category.assoc]
  rfl

/-- **The shift of a pairing along a postcomposition**: for `H : D ⥤ D'` additive and compatible
with the shifts, the shift of `H(ψ)` for `G ⋙ H` is `H` of the shift of `ψ` for `G`. -/
theorem shiftedPairing_postcompInt (G : C₁ ⥤ C₂ ⥤ D) [G.CommShift₂Int] (H : D ⥤ D')
    [H.CommShift ℤ] [H.Additive] {K : C₁} {L : C₂} {M : D} (ψ : (G.obj K).obj L ⟶ M) (n m : ℤ)
    (h : n + m = 0) :
    (G ⋙ (whiskeringRight C₂ D D').obj H).shiftedPairing (H.map ψ) n m h =
      H.map (G.shiftedPairing ψ n m h) := by
  have e₁ : (((G ⋙ (whiskeringRight C₂ D D').obj H).obj (K⟦n⟧)).commShiftIso m).hom.app L =
      H.map (((G.obj (K⟦n⟧)).commShiftIso m).hom.app L) ≫
        (H.commShiftIso m).hom.app ((G.obj (K⟦n⟧)).obj L) :=
    Functor.commShiftIso_comp_hom_app (G.obj (K⟦n⟧)) H m L
  have e₂ : (((G ⋙ (whiskeringRight C₂ D D').obj H).flip.obj L).commShiftIso n).hom.app K =
      H.map (((G.flip.obj L).commShiftIso n).hom.app K) ≫
        (H.commShiftIso n).hom.app ((G.obj K).obj L) :=
    Functor.commShiftIso_comp_hom_app (G.flip.obj L) H n K
  have e₃ := H.map_shiftFunctorCompIsoId_hom_app ((G.obj K).obj L) n m h
  have e₄ := H.commShiftIso_hom_naturality (((G.flip.obj L).commShiftIso n).hom.app K) m
  simp only [shiftedPairing, e₁, e₂, Functor.map_comp, Category.assoc, e₃]
  simp only [Functor.comp_obj, Functor.flip_obj_obj] at e₄
  rw [reassoc_of% e₄]
  rfl

/-- **The shift of a pairing for the currying of a postcomposite** `uncurry G ⋙ H`, with the
datum transported along `CategoryTheory.Functor.curryObjUncurryObjCompIso`, is the shift for the
postcomposite `G ⋙ H` of bifunctors. -/
theorem shiftedPairing_curryObjUncurryObjComp (G : C₁ ⥤ C₂ ⥤ D) [G.CommShift₂Int] (H : D ⥤ D')
    [H.CommShift ℤ] [H.Additive] {K : C₁} {L : C₂} {M : D'}
    (φ : H.obj ((G.obj K).obj L) ⟶ M) (n m : ℤ) (h : n + m = 0) :
    letI := CommShift₂.ofIsoInt (curryObjUncurryObjCompIso G H)
    (curry.obj (uncurry.obj G ⋙ H)).shiftedPairing φ n m h =
      (G ⋙ (whiskeringRight C₂ D D').obj H).shiftedPairing φ n m h := by
  let := CommShift₂.ofIsoInt (curryObjUncurryObjCompIso G H)
  have := CommShift₂.ofIsoInt_commShift₂ (curryObjUncurryObjCompIso G H)
  have e := shiftedPairing_natTrans (curryObjUncurryObjCompIso G H).hom φ n m h
  rw [curryObjUncurryObjCompIso_hom_app_app, curryObjUncurryObjCompIso_hom_app_app] at e
  exact (Category.id_comp _).symm.trans (e.symm.trans
    (congrArg (fun x => (G ⋙ (whiskeringRight C₂ D D').obj H).shiftedPairing x n m h)
      (Category.id_comp φ)))

end CategoryTheory.Functor
