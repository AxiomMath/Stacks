module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.DeducingFullyFaithfulness.ResidueFieldSkyscraperCoherent
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.DeducingFullyFaithfulness.ResidueFieldSkyscraperPushforward
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Coherent
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.StalkRingComparison
public import Mathlib.AlgebraicGeometry.Stalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
public import StacksFrontier.Topology.Dimension.Krull
public import StacksFrontier.Topology.Sheaves.Modules.StalkExactness
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# The residue-field skyscraper at a closed point is coherent

Let `X` be a scheme and `x` a closed point of `X`. The skyscraper sheaf `𝒪_x` at `x` with value
`κ(x)` (`AlgebraicGeometry.residueFieldSkyscraperSheaf`) is the direct image of the structure sheaf
along the closed immersion `i : Spec κ(x) ⟶ X`; in particular it is coherent when `X` is locally
Noetherian.

On the one-point scheme `Spec K` of a field the evaluation morphism `𝒪 ⟶ 𝒪_z`, the morphism out of
the structure sheaf given by the constant section `1` of the skyscraper, is an isomorphism: over
the whole space it is `K = Γ(Spec K, 𝒪) ⟶ 𝒪_z ⟶ κ(z)`, a composite of isomorphisms, and over the
empty open both sides are zero. The general case is the direct image of that one along `i`, which
is `AlgebraicGeometry.pushforwardResidueFieldSkyscraperIso`.

## Main results

* `Stacks.AlgebraicGeometry.DerivedVarieties.Orlov.isIso_evalResidueField`: on `Spec K`, the
  evaluation morphism `𝒪 ⟶ 𝒪_z` is an isomorphism.
* `Stacks.AlgebraicGeometry.DerivedVarieties.Orlov.residueFieldSkyscraperSheafIsoPushforward`:
  `𝒪_x ≅ i_*𝒪_{Spec κ(x)}` for a closed point `x`.

That `𝒪_x` is coherent on a locally Noetherian scheme is
`AlgebraicGeometry.isCoherent_residueFieldSkyscraperSheaf`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.DerivedVarieties.Orlov

/-- Over a local ring which is a field, the residue field map `A ⟶ κ(𝔪)` is bijective. -/
theorem bijective_algebraMap_residueField_of_isField {A : Type u} [CommRing A] [IsLocalRing A]
    (hA : IsField A) :
    Function.Bijective (algebraMap A (IsLocalRing.maximalIdeal A).ResidueField) := by
  refine ⟨?_, fun t => ?_⟩
  · rw [RingHom.injective_iff_ker_eq_bot, Ideal.ker_algebraMap_residueField]
    exact (IsLocalRing.isField_iff_maximalIdeal_eq).1 hA
  · obtain ⟨q, rfl⟩ :=
      (IsLocalRing.maximalIdeal A).bijective_algebraMap_quotient_residueField.2 t
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact ⟨a, rfl⟩

section Evaluation

variable (Z : Scheme.{u}) (z : Z)

/-- The constant section `1` of the residue-field skyscraper at `z`. -/
def residueFieldSkyscraperOne : (residueFieldSkyscraperSheaf Z z).sections :=
  ⟨fun _ _ => (1 : (IsLocalRing.maximalIdeal
      (ToType (StacksDraft.StalkRingComparison.stalkRing Z z))).ResidueField), fun _ => rfl⟩

/-- **The evaluation morphism `𝒪_Z ⟶ 𝒪_z`**: the morphism out of the structure sheaf given by the
constant section `1` of the skyscraper. Over an open `U ∋ z` it sends a section to the image in
`κ(z)` of its germ. -/
def evalResidueField : SheafOfModules.unit Z.ringCatSheaf ⟶ residueFieldSkyscraperSheaf Z z :=
  (residueFieldSkyscraperSheaf Z z).unitHomEquiv.symm (residueFieldSkyscraperOne Z z)

/-- The stalk ring of `Spec K` at its closed point is a field. -/
private theorem isField_stalkRing_closedPoint (K : Type u) [Field K] :
    IsField (ToType (StacksDraft.StalkRingComparison.stalkRing (Spec (CommRingCat.of K))
      (IsLocalRing.closedPoint K))) :=
  MulEquiv.isField (Field.toIsField K)
    ((StacksDraft.StalkRingComparison.stalkRingEquiv (Spec (CommRingCat.of K))
      (IsLocalRing.closedPoint K)).trans
      (AlgebraicGeometry.stalkClosedPointIso
        (CommRingCat.of K)).commRingCatIsoToRingEquiv).toMulEquiv

/-- On `Spec K`, the germ of global sections at the closed point is bijective. -/
private theorem bijective_germ_top_closedPoint (K : Type u) [Field K] :
    Function.Bijective
      ((Spec (CommRingCat.of K)).presheaf.germ ⊤ (IsLocalRing.closedPoint K) trivial) := by
  rw [← AlgebraicGeometry.ΓSpecIso_hom_stalkClosedPointIso_inv]
  exact ((Scheme.ΓSpecIso (CommRingCat.of K)).trans
    (AlgebraicGeometry.stalkClosedPointIso
      (CommRingCat.of K)).symm).commRingCatIsoToRingEquiv.bijective

/-- **On the spectrum of a field the evaluation morphism `𝒪 ⟶ 𝒪_z` is an isomorphism.** It is
checked on sections: over the whole space it is `Γ(Spec K, 𝒪) ⟶ 𝒪_z ⟶ κ(z)`, bijective because
`Γ(Spec K, 𝒪)` is a field, every germ at the only point is the germ of a global section, and the
stalk maps onto its residue field; over the empty open both sides are zero. -/
theorem isIso_evalResidueField (K : Type u) [Field K] (z : Spec (CommRingCat.of K)) :
    IsIso (evalResidueField (Spec (CommRingCat.of K)) z) := by
  let Z := Spec (CommRingCat.of K)
  let F := SheafOfModules.forget Z.ringCatSheaf ⋙ PresheafOfModules.toPresheaf _
  suffices IsIso (F.map (evalResidueField Z z)) from isIso_of_reflects_iso _ F
  rw [NatTrans.isIso_iff_isIso_app]
  intro U
  rw [ConcreteCategory.isIso_iff_bijective]
  obtain ⟨V⟩ := U
  obtain rfl : z = IsLocalRing.closedPoint K := Subsingleton.elim _ _
  rcases eq_bot_or_eq_top V with rfl | rfl
  · refine ⟨fun a b _ => Subsingleton.elim (α := Γ(Z, ⊥)) a b, fun t => ⟨0, funext fun h => ?_⟩⟩
    exact (h.down.elim : False).elim
  · let z := IsLocalRing.closedPoint K
    let : CommRing (ToType (StacksDraft.StalkRingComparison.stalkRing Z z)) :=
      StacksDraft.StalkRingComparison.commRingStalkRing Z z
    let : IsLocalRing (ToType (StacksDraft.StalkRingComparison.stalkRing Z z)) :=
      StacksDraft.StalkRingComparison.isLocalRing_stalkRing Z z
    let g : Γ(Z, ⊤) → (IsLocalRing.maximalIdeal
        (ToType (StacksDraft.StalkRingComparison.stalkRing Z z))).ResidueField := fun r =>
      algebraMap (ToType (StacksDraft.StalkRingComparison.stalkRing Z z)) _
      ((StacksDraft.StalkRingComparison.stalkRingEquiv Z z).symm (Z.presheaf.germ ⊤ z trivial r))
    have hg : Function.Bijective g := (bijective_algebraMap_residueField_of_isField
      (isField_stalkRing_closedPoint K)).comp
      ((StacksDraft.StalkRingComparison.stalkRingEquiv Z z).symm.bijective.comp
        (bijective_germ_top_closedPoint K))
    have : Unique (PLift (z ∈ (⊤ : Opens Z))) := ⟨⟨⟨trivial⟩⟩, fun _ => rfl⟩
    let e := Equiv.funUnique (PLift (z ∈ (⊤ : Opens Z)))
      (IsLocalRing.maximalIdeal
        (ToType (StacksDraft.StalkRingComparison.stalkRing Z z))).ResidueField
    have heq : ∀ r : Γ(Z, ⊤),
        (ConcreteCategory.hom ((F.map (evalResidueField Z z)).app (op ⊤))) r = e.symm (g r) := by
      intro r
      funext h
      have key : ∀ a : ToType (StacksDraft.StalkRingComparison.stalkRing Z z),
          a • (1 : (IsLocalRing.maximalIdeal
            (ToType (StacksDraft.StalkRingComparison.stalkRing Z z))).ResidueField) =
            algebraMap _ _ a := fun a => (Algebra.algebraMap_eq_smul_one a).symm
      refine (key ((TopCat.Presheaf.germ (C := RingCat.{u}) Z.ringCatSheaf.obj ⊤ z
        trivial).hom r)).trans ?_
      change _ = g r
      congr 1
      exact (RingEquiv.eq_symm_apply _).2
        (StacksDraft.StalkRingComparison.stalkRingEquiv_germ Z z ⊤ trivial r)
    refine ⟨fun a b hab => hg.1 (e.symm.injective ((heq a).symm.trans (hab.trans (heq b)))),
      fun t => ?_⟩
    obtain ⟨r, hr⟩ := hg.2 (e t)
    exact ⟨r, (heq r).trans (by rw [hr]; exact e.symm_apply_apply t)⟩

end Evaluation

/-! ### Support -/

section Support

variable (X : Scheme.{u}) (x : X)

/-- A point lies in the support of a sheaf of `𝒪_X`-modules exactly when the stalk there is
nonzero. -/
theorem mem_supp_iff_not_isZero_stalkFunctor (M : X.Modules) (y : X) :
    y ∈ SheafOfModules.supp M ↔
      ¬ IsZero ((SheafOfModules.stalkFunctor X.ringCatSheaf y).obj M) := by
  refine (SheafOfModules.mem_supp_iff_nontrivial_stalk (R := X.ringCatSheaf) M y).trans ?_
  refine Iff.trans ?_ (not_congr (SheafOfModules.isZero_stalkFunctor_obj_iff
    X.ringCatSheaf y M).symm)
  rw [AddCommGrpCat.isZero_iff_subsingleton, not_subsingleton_iff_nontrivial]

/-- The stalk of the residue-field skyscraper at `x` is `κ(x)`, which is nonzero. -/
theorem not_isZero_stalkFunctor_residueFieldSkyscraperSheaf :
    ¬ IsZero ((SheafOfModules.stalkFunctor X.ringCatSheaf x).obj
      (residueFieldSkyscraperSheaf X x)) := fun h =>
  not_subsingleton (IsLocalRing.maximalIdeal
    (ToType (StacksDraft.StalkRingComparison.stalkRing X x))).ResidueField
    (ModuleCat.subsingleton_of_isZero (h.of_iso (SheafOfModules.skyscraperStalkIsoObj
      X.ringCatSheaf x (residueFieldStalkModule X x)).symm))

/-- The stalk of the residue-field skyscraper at a closed point `x` vanishes away from `x`. -/
theorem isZero_stalkFunctor_residueFieldSkyscraperSheaf_of_ne (hx : IsClosed ({x} : Set X))
    {y : X} (hy : y ≠ x) :
    IsZero ((SheafOfModules.stalkFunctor X.ringCatSheaf y).obj
      (residueFieldSkyscraperSheaf X x)) := by
  rw [SheafOfModules.isZero_stalkFunctor_obj_iff, AddCommGrpCat.isZero_iff_subsingleton]
  refine ⟨fun a b => ?_⟩
  suffices ∀ t : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (residueFieldSkyscraperSheaf X x).val.presheaf y, t = 0 by rw [this a, this b]
  intro t
  obtain ⟨U, hyU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq
    (residueFieldSkyscraperSheaf X x).val.presheaf (x := y) t
  let V : Opens X := ⟨{x}ᶜ, hx.isOpen_compl⟩
  have hyW : y ∈ U ⊓ V := ⟨hyU, hy⟩
  rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE (inf_le_left : U ⊓ V ≤ U)) y hyW s]
  have hsub : Subsingleton ((residueFieldSkyscraperSheaf X x).val.presheaf.obj (op (U ⊓ V))) :=
    ⟨fun f g => funext fun h => (h.down.2 rfl).elim⟩
  rw [Subsingleton.elim ((residueFieldSkyscraperSheaf X x).val.presheaf.map
    (homOfLE (inf_le_left : U ⊓ V ≤ U)).op s) 0, map_zero]

/-- **The support of the residue-field skyscraper at a closed point `x` is `{x}`.** -/
theorem supp_residueFieldSkyscraperSheaf (hx : IsClosed ({x} : Set X)) :
    SheafOfModules.supp (residueFieldSkyscraperSheaf X x) = {x} := by
  ext y
  refine (mem_supp_iff_not_isZero_stalkFunctor X _ y).trans ?_
  rw [Set.mem_singleton_iff]
  refine ⟨fun h => ?_, fun h => h ▸ not_isZero_stalkFunctor_residueFieldSkyscraperSheaf X x⟩
  by_contra hne
  exact h (isZero_stalkFunctor_residueFieldSkyscraperSheaf_of_ne X x hx hne)

/-- **The support of the residue-field skyscraper at a closed point has dimension zero.** -/
theorem topologicalKrullDim_supp_residueFieldSkyscraperSheaf (hx : IsClosed ({x} : Set X)) :
    topologicalKrullDim (SheafOfModules.supp (residueFieldSkyscraperSheaf X x)) = 0 := by
  rw [supp_residueFieldSkyscraperSheaf X x hx]
  exact le_antisymm (topologicalKrullDim_zero_of_discreteTopology _)
    (Order.krullDim_nonneg_iff.mpr
      ⟨⟨closure {⟨x, rfl⟩}, isIrreducible_singleton.closure, isClosed_closure⟩⟩)

end Support

end Stacks.AlgebraicGeometry.DerivedVarieties.Orlov

end
