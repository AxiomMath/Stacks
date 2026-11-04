module

public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.RankOneInvertibleOpen
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.CodimTwoInvertibleClass

/-!
# The Weil divisor class of a rank one coherent reflexive module

Let `X` be an integral locally Noetherian normal scheme.  A rank one coherent reflexive
`𝒪_X`-module `ℱ` is invertible on an open subscheme `U` whose complement has codimension at
least two, and the class of `ℱ|_U` in `Cl(U) = Cl(X)` does not depend on the choice of `U`.
This is the map of [Stacks, Tag 0EBM] from isomorphism classes of rank one coherent reflexive
modules to `Cl(X)`, and it is injective.

## Main definitions

* `AlgebraicGeometry.CoherentReflexive.rankOneWeilClass` — the class in `Cl(X)` of a rank one
  coherent reflexive module.
* `AlgebraicGeometry.CoherentReflexive.rankOneSkeletonToWeilClass` — the induced map on
  isomorphism classes.

## Main results

* `AlgebraicGeometry.CoherentReflexive.rankOneWeilClass_eq` — it is computed on any open whose
  complement has codimension at least two and on which the module is invertible.
* `AlgebraicGeometry.CoherentReflexive.rankOneSkeletonToWeilClass_injective` — the induced map on
  isomorphism classes is injective.
* `AlgebraicGeometry.CoherentReflexive.rankOneSkeletonToWeilClass_surjective_iff` — it is
  surjective exactly when every divisor class is the class of an invertible module on some open
  whose complement has codimension at least two.

## References

* [Stacks Project, Tag 0EBM](https://stacks.math.columbia.edu/tag/0EBM)
-/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules (IsReflexive)

universe u

namespace AlgebraicGeometry.CoherentReflexive

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

omit [IsIntegral X] [IsLocallyNoetherian X] in
/-- Invertibility on an open passes to a smaller open. -/
theorem isInvertible_restrict_of_le {U V : X.Opens} (h : U ≤ V) (F : X.Modules)
    (hF : SheafOfModules.IsInvertible V.toScheme.sheaf.obj V.toScheme.ringCatSheaf.property
      (F.restrict V.ι)) :
    SheafOfModules.IsInvertible U.toScheme.sheaf.obj U.toScheme.ringCatSheaf.property
      (F.restrict U.ι) :=
  Stacks.UFDExtensionGlobal.isInvertible_of_iso
    (Stacks.UFDExtensionGlobal.restrictCongrComp
      (show X.homOfLE h ≫ V.ι = U.ι by simp) F).symm
    (Stacks.UFDExtensionGlobal.isInvertible_restrict (X.homOfLE h) (F.restrict V.ι) hF)

/-- **The class of an invertible restriction does not depend on the open subscheme**, among
opens whose complement has codimension at least two. -/
theorem weilClassOfCodimTwoInvertible_restrict_independent (F : X.Modules) (U V : X.Opens)
    (hU : ∀ x : X, x ∉ U → (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x))
    (hV : ∀ x : X, x ∉ V → (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x))
    (hFU) (hFV) :
    weilClassOfCodimTwoInvertible U hU (F.restrict U.ι) hFU =
      weilClassOfCodimTwoInvertible V hV (F.restrict V.ι) hFV := by
  have hW := two_le_codimension_compl_inf U V hU hV
  have key : ∀ (T : X.Opens) (hT : ∀ x : X, x ∉ T →
        (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x))
      (hWT : U ⊓ V ≤ T) (hFT), weilClassOfCodimTwoInvertible (U ⊓ V) hW
        (F.restrict (U ⊓ V).ι) (isInvertible_restrict_of_le hWT F hFT) =
        weilClassOfCodimTwoInvertible T hT (F.restrict T.ι) hFT := by
    intro T hT hWT hFT
    have h1 : weilClassOfCodimTwoInvertible (U ⊓ V) hW (F.restrict (U ⊓ V).ι)
          (isInvertible_restrict_of_le hWT F hFT) =
        weilClassOfCodimTwoInvertible (U ⊓ V) hW ((F.restrict T.ι).restrict (X.homOfLE hWT))
          (Stacks.UFDExtensionGlobal.isInvertible_restrict (X.homOfLE hWT)
            (F.restrict T.ι) hFT) :=
      weilClassOfCodimTwoInvertible_congr (U ⊓ V) hW _ _
        (Stacks.UFDExtensionGlobal.restrictCongrComp
          (show X.homOfLE hWT ≫ T.ι = (U ⊓ V).ι by simp) F)
    exact h1.trans (weilClassOfCodimTwoInvertible_restrict (U ⊓ V) hW hT hWT
      (F.restrict T.ι) hFT _)
  exact (key U hU inf_le_left hFU).symm.trans (key V hV inf_le_right hFV)

variable [IsNormal X]

/-- **The Weil divisor class of a rank one coherent reflexive module**: the class of its
restriction to any open subscheme whose complement has codimension at least two and on which it
is invertible, read in `Cl(X)` through `Cl(X) ≅ Cl(U)`. -/
def rankOneWeilClass (F : RankOneReflexiveModules X) : weilDivisorClassGroup X :=
  weilClassOfCodimTwoInvertible (exists_codimTwo_isInvertible_restrict F).choose
    (exists_codimTwo_isInvertible_restrict F).choose_spec.1 _
    (exists_codimTwo_isInvertible_restrict F).choose_spec.2

/-- The Weil divisor class of a rank one coherent reflexive module is computed on *any* open
subscheme whose complement has codimension at least two and on which it is invertible. -/
theorem rankOneWeilClass_eq (F : RankOneReflexiveModules X) (U : X.Opens)
    (hU : ∀ x : X, x ∉ U → (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x))
    (hFU) : rankOneWeilClass F = weilClassOfCodimTwoInvertible U hU (F.module.restrict U.ι) hFU :=
  weilClassOfCodimTwoInvertible_restrict_independent F.module _ U _ hU _ hFU

/-- Two rank one coherent reflexive modules with the same Weil divisor class are isomorphic, and
conversely. -/
theorem rankOneWeilClass_eq_iff (F G : RankOneReflexiveModules X) :
    rankOneWeilClass F = rankOneWeilClass G ↔ Nonempty (F.module ≅ G.module) := by
  obtain ⟨U, hU, hFU⟩ := exists_codimTwo_isInvertible_restrict F
  obtain ⟨V, hV, hGV⟩ := exists_codimTwo_isInvertible_restrict G
  have hW := two_le_codimension_compl_inf U V hU hV
  rw [rankOneWeilClass_eq F (U ⊓ V) hW (isInvertible_restrict_of_le inf_le_left _ hFU),
    rankOneWeilClass_eq G (U ⊓ V) hW (isInvertible_restrict_of_le inf_le_right _ hGV),
    weilClassOfCodimTwoInvertible_eq_iff (U ⊓ V) hW]
  exact nonempty_iso_restrict_iff (U ⊓ V) hW F G

/-- Isomorphic rank one coherent reflexive modules have the same Weil divisor class. -/
theorem rankOneWeilClass_congr {F G : RankOneReflexiveModules X} (e : F ≅ G) :
    rankOneWeilClass F = rankOneWeilClass G :=
  (rankOneWeilClass_eq_iff F G).2 ⟨⟨e.hom.hom.hom.hom, e.inv.hom.hom.hom,
    congrArg (fun f : F ⟶ F => f.hom.hom.hom) e.hom_inv_id,
    congrArg (fun f : G ⟶ G => f.hom.hom.hom) e.inv_hom_id⟩⟩

/-- **The map of [Stacks, Tag 0EBM] from isomorphism classes of rank one coherent reflexive
modules to the Weil divisor class group.** -/
def rankOneSkeletonToWeilClass (c : Skeleton (RankOneReflexiveModules X)) :
    weilDivisorClassGroup X :=
  rankOneWeilClass ((fromSkeleton (RankOneReflexiveModules X)).obj c)

/-- The value of `rankOneSkeletonToWeilClass` on the isomorphism class of `F` is
`rankOneWeilClass F`. -/
theorem rankOneSkeletonToWeilClass_toSkeleton (F : RankOneReflexiveModules X) :
    rankOneSkeletonToWeilClass (toSkeleton F) = rankOneWeilClass F :=
  rankOneWeilClass_congr (fromSkeletonToSkeletonIso F)

/-- **The map of [Stacks, Tag 0EBM] is injective.** -/
theorem rankOneSkeletonToWeilClass_injective :
    Function.Injective (rankOneSkeletonToWeilClass (X := X)) := by
  intro c d h
  obtain ⟨F, rfl⟩ : ∃ F, toSkeleton F = c := ⟨_, toSkeleton_fromSkeleton_obj c⟩
  obtain ⟨G, rfl⟩ : ∃ G, toSkeleton G = d := ⟨_, toSkeleton_fromSkeleton_obj d⟩
  rw [rankOneSkeletonToWeilClass_toSkeleton, rankOneSkeletonToWeilClass_toSkeleton] at h
  obtain ⟨i⟩ := (rankOneWeilClass_eq_iff F G).1 h
  exact toSkeleton_eq_toSkeleton_iff.2
    ⟨(ObjectProperty.ι _).preimageIso ((ObjectProperty.ι _).preimageIso
      ((ObjectProperty.ι _).preimageIso i))⟩

/-- **The map of [Stacks, Tag 0EBM] is surjective exactly when every Weil divisor class is the
class of an invertible module on an open whose complement has codimension at least two.** -/
theorem rankOneSkeletonToWeilClass_surjective_iff :
    Function.Surjective (rankOneSkeletonToWeilClass (X := X)) ↔
      ∀ c : weilDivisorClassGroup X, ∃ (U : X.Opens)
        (hU : ∀ x : X, x ∉ U → (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x))
        (L : U.toScheme.Modules) (hL : SheafOfModules.IsInvertible U.toScheme.sheaf.obj
          U.toScheme.ringCatSheaf.property L), weilClassOfCodimTwoInvertible U hU L hL = c := by
  constructor
  · intro hsurj c
    obtain ⟨d, hd⟩ := hsurj c
    obtain ⟨F, rfl⟩ : ∃ F, toSkeleton F = d := ⟨_, toSkeleton_fromSkeleton_obj d⟩
    obtain ⟨U, hU, hFU⟩ := exists_codimTwo_isInvertible_restrict F
    refine ⟨U, hU, F.module.restrict U.ι, hFU, ?_⟩
    rwa [← rankOneWeilClass_eq F U hU hFU, ← rankOneSkeletonToWeilClass_toSkeleton]
  · intro h c
    obtain ⟨U, hU, L, hL, hLc⟩ := h c
    obtain ⟨F, ⟨e⟩⟩ := exists_rankOne_of_isInvertible U hU L hL
    refine ⟨toSkeleton F, ?_⟩
    rwa [rankOneSkeletonToWeilClass_toSkeleton,
      rankOneWeilClass_eq F U hU (Stacks.UFDExtensionGlobal.isInvertible_of_iso e.symm hL),
      weilClassOfCodimTwoInvertible_congr U hU _ hL e]

end AlgebraicGeometry.CoherentReflexive

end
