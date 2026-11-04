module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExteriorSymmetricConstruction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.Sectionwise

/-!
# Restriction to a slice site commutes with the symmetric and tensor powers

Quasi-coherence of a sheaf of modules is a condition on the *slice sites*: a
`SheafOfModules.QuasicoherentData` presents `M.over (X i)` over the topology `J.over (X i)`, for
a family `X` covering the terminal object. So in order to deduce quasi-coherence of a symmetric
power `Symⁿ F` from a local trivialization of `F`, one first has to know that `Symⁿ` commutes
with restriction to a slice site — the case of Tag 01CI for an open immersion, which
`SheafOfModules.GradedAlgebra.pullbackComparison` supplies only as a morphism.

This file proves that commutation, degreewise, for the symmetric and the tensor powers of
`SheafOfModules.sheafifiedSymmetricAlgebra` and `SheafOfModules.sheafifiedTensorAlgebra`, and
records the reduction of Tag 01CK that it buys. It is proved in two independent halves:

* **the sheafification half**, `sheafificationRestrictionIso`, which holds for an arbitrary
  continuous *and cocontinuous* functor of sites and is the module-level counterpart of
  `Stacks.SheafOfModules.sheafificationWhiskerIso`;
* **the sectionwise half**, `pushforward₀_symmetricAlgebraPiece`, which holds on the nose: the
  presheaf `U ↦ Symⁿ_{O(U)}(F(U))` is defined section by section, so precomposing with a functor
  of sites commutes with it definitionally.

`Over.forget Y` is both continuous and cocontinuous for `J.over Y` and `J`, so the two halves
compose to `symmetricPieceOverIso`.

## Main definitions

* `Stacks.SliceAlgebra.sheafificationRestrictionComparison`: the comparison morphism from the
  sheafification of a restricted presheaf of modules to the restriction of its sheafification,
  as the adjoint transpose of the restricted sheafification unit.
* `Stacks.SliceAlgebra.symmetricPieceOverIso`, `Stacks.SliceAlgebra.tensorPieceOverIso`: the
  degree-`n` symmetric (resp. tensor) power of the restriction of `F` to the slice site over `Y`
  is the restriction of the degree-`n` symmetric (resp. tensor) power of `F`.

## Main results

* `Stacks.SliceAlgebra.isIso_sheafificationRestrictionComparison`: **restriction along a
  continuous cocontinuous functor of sites commutes with sheafification of presheaves of
  modules.**
* `Stacks.SliceAlgebra.pushforward₀_symmetricAlgebraPiece`,
  `Stacks.SliceAlgebra.pushforward₀_tensorAlgebraPiece`: the sectionwise powers commute with
  restriction definitionally.
* `Stacks.SliceAlgebra.isQuasicoherent_piece_of_presentations`: quasi-coherence of `Symⁿ F`
  follows from a presentation of the degree-`n` symmetric power of `F.over (X i)` for each member
  of a covering family. This is the sheaf-theoretic clause (5) of Tag 01CK with the
  slice-restriction obligation discharged.

## Implementation notes

**No `@[stacks]` tag.** Tag 01CI asserts `f^*Sym(F) = Sym(f^*F)` for an arbitrary morphism of
ringed spaces, compatibly with multiplication, the unit and the degree-one generators. What is
proved here is the special case of a restriction to a slice site, degreewise, on the underlying
sheaves of modules only — enough for quasi-coherence, which is a property of the underlying
sheaf, and not the content of the tag.

**Why the statements are generic in the functor of sites.** Stating the sectionwise commutation
at the concrete `SheafOfModules.over` exhausts the elaborator's budget at `whnf`: the two
`PresheafOfModules` structures are definitionally equal but not syntactically so, and comparing
their `map`, `map_id` and `map_comp` fields unfolds `SymPow.symmetricPowerInt` on both sides.
Stated for an abstract functor `H` and an abstract presheaf of commutative rings, where
`isDefEq` has nothing to unfold, the same statement is `rfl`, and the specialization to
`Over.forget Y` then only ever compares terms with the same head symbol. The same reason splits
`pushforward_obj_eq_pushforward₀_obj` and `restrictScalars_id_obj` out as separate steps: the
restriction of scalars along an identity is invisible objectwise but not structurally.

**What is still missing for Tag 01CK.** `isQuasicoherent_piece_of_presentations` leaves exactly
one obligation: a presentation of the degree-`n` symmetric power of a sheaf of modules that has
a global presentation. That is Tag 01CJ at the sheaf level, together with the freeness of a
symmetric power of a free sheaf of modules, which is available for plain modules
(`SymPow.free_symmetricPower`) but not for sheaves. Of Tag 01CJ the surjectivity half is
`SheafOfModules.epi_descComp_app_symmetric`: the degree-`n` symmetric power of an epimorphism of
sheaves of modules is an epimorphism, in every degree and over an arbitrary site. Exactness at
the middle term is not proved here.

**The exterior analogue is absent on purpose.** The same statement for `exteriorAlgebraPiece`
does *not* elaborate by `rfl` inside the default budget, where the symmetric and tensor ones do;
nothing is claimed about it here. It is not needed by
Tag 01OB and is left out rather than bought with a raised budget.

## References

* [Stacks Project, Tag 01CI](https://stacks.math.columbia.edu/tag/01CI)
* [Stacks Project, Tag 01CJ](https://stacks.math.columbia.edu/tag/01CJ)
* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open CategoryTheory Category Opposite PresheafOfModules CategoryTheory.Sheaf

universe v v₁ v₂ u₁ u₂ t w a

namespace Stacks.SliceAlgebra

/-! ### Restriction and sheafification -/

section Sheafification

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (H : C ⥤ D)
  [H.IsContinuous J K] [H.IsCocontinuous J K]
  {R₀ : Dᵒᵖ ⥤ RingCat.{t}} (R : Sheaf K RingCat.{t})

/-- The restriction of a sheaf of rings along a continuous functor of sites. -/
abbrev restrictedRing : Sheaf J RingCat.{t} :=
  (H.sheafPushforwardContinuous RingCat.{t} J K).obj R

variable {R} (α : R₀ ⟶ R.obj)

/-- The restriction of a morphism from a presheaf of rings to a sheaf of rings. -/
abbrev restrictedRingMap : (H.op ⋙ R₀) ⟶ (restrictedRing J K H R).obj :=
  Functor.whiskerLeft H.op α

variable [Presheaf.IsLocallyInjective K α] [Presheaf.IsLocallySurjective K α]

omit [H.IsContinuous J K] [Presheaf.IsLocallySurjective K α] in
/-- The restriction of a locally injective morphism of presheaves of rings along a cocontinuous
functor of sites is locally injective. -/
instance isLocallyInjective_restrictedRingMap :
    Presheaf.IsLocallyInjective J (restrictedRingMap J K H α) :=
  Presheaf.isLocallyInjective_whisker J K H α

omit [H.IsContinuous J K] [Presheaf.IsLocallyInjective K α] in
/-- The restriction of a locally surjective morphism of presheaves of rings along a cocontinuous
functor of sites is locally surjective. -/
instance isLocallySurjective_restrictedRingMap :
    Presheaf.IsLocallySurjective J (restrictedRingMap J K H α) :=
  Presheaf.isLocallySurjective_whisker J K H α

variable [K.WEqualsLocallyBijective AddCommGrpCat.{v}] [HasWeakSheafify K AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}] [HasWeakSheafify J AddCommGrpCat.{v}]

/-- **The comparison morphism between the sheafification of a restricted presheaf of modules and
the restriction of its sheafification**, as the adjoint transpose of the restricted
sheafification unit. -/
noncomputable def sheafificationRestrictionComparison (Q : PresheafOfModules.{v} R₀) :
    (PresheafOfModules.sheafification (restrictedRingMap J K H α)).obj
        ((PresheafOfModules.pushforward₀ H R₀).obj Q) ⟶
      (SheafOfModules.pushforward (𝟙 (restrictedRing J K H R))).obj
        ((PresheafOfModules.sheafification α).obj Q) :=
  (PresheafOfModules.sheafificationHomEquiv (restrictedRingMap J K H α)).symm
    ((PresheafOfModules.pushforward₀ H R₀).map
      ((PresheafOfModules.sheafificationAdjunction α).unit.app Q))

/-- **Restriction along a continuous cocontinuous functor of sites commutes with sheafification
of presheaves of modules.** The restricted sheafification unit and the sheafification unit of the
restricted presheaf are both locally bijective, so the morphism of sheafifications they factor
through is too; `SheafOfModules.toSheaf` then reflects the isomorphism. -/
instance isIso_sheafificationRestrictionComparison (Q : PresheafOfModules.{v} R₀) :
    IsIso (sheafificationRestrictionComparison J K H α Q) := by
  have : Presheaf.IsLocallyInjective K (CategoryTheory.toSheafify K Q.presheaf) :=
    (K.W_toSheafify Q.presheaf).isLocallyInjective
  have : Presheaf.IsLocallySurjective K (CategoryTheory.toSheafify K Q.presheaf) :=
    (K.W_toSheafify Q.presheaf).isLocallySurjective
  have : Presheaf.IsLocallyInjective J
      (Functor.whiskerLeft H.op (CategoryTheory.toSheafify K Q.presheaf)) :=
    Presheaf.isLocallyInjective_whisker J K H _
  have : Presheaf.IsLocallySurjective J
      (Functor.whiskerLeft H.op (CategoryTheory.toSheafify K Q.presheaf)) :=
    Presheaf.isLocallySurjective_whisker J K H _
  have hiso : IsIso ((SheafOfModules.toSheaf (restrictedRing J K H R)).map
      (sheafificationRestrictionComparison J K H α Q)) := by
    have e : (SheafOfModules.toSheaf (restrictedRing J K H R)).map
        (sheafificationRestrictionComparison J K H α Q) =
        ((CategoryTheory.sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv
            ((PresheafOfModules.pushforward₀ H R₀).obj Q).presheaf
            ((SheafOfModules.toSheaf (restrictedRing J K H R)).obj
              ((SheafOfModules.pushforward (𝟙 (restrictedRing J K H R))).obj
                ((PresheafOfModules.sheafification α).obj Q)))).symm
          (Functor.whiskerLeft H.op (CategoryTheory.toSheafify K Q.presheaf)) :=
      PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm _ _
    rw [e]
    apply (J.W_sheafToPresheaf_map_iff_isIso _).mp
    have h := (J.W_iff_isLocallyBijective
      (Functor.whiskerLeft H.op (CategoryTheory.toSheafify K Q.presheaf))).mpr
      ⟨inferInstance, inferInstance⟩
    have hfac : CategoryTheory.toSheafify J
          ((PresheafOfModules.pushforward₀ H R₀).obj Q).presheaf ≫
        (sheafToPresheaf J AddCommGrpCat.{v}).map
          (((CategoryTheory.sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv
            ((PresheafOfModules.pushforward₀ H R₀).obj Q).presheaf
            ((SheafOfModules.toSheaf (restrictedRing J K H R)).obj
              ((SheafOfModules.pushforward (𝟙 (restrictedRing J K H R))).obj
                ((PresheafOfModules.sheafification α).obj Q)))).symm
            (Functor.whiskerLeft H.op (CategoryTheory.toSheafify K Q.presheaf))) =
        Functor.whiskerLeft H.op (CategoryTheory.toSheafify K Q.presheaf) :=
      CategoryTheory.toSheafify_sheafifyLift J _ _
    rw [← hfac] at h
    exact J.W.of_precomp (W' := J.W) _ _ (J.W_toSheafify _) h
  exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf (restrictedRing J K H R))

/-- **Restriction commutes with sheafification of presheaves of modules**, as an isomorphism. -/
noncomputable def sheafificationRestrictionIso (Q : PresheafOfModules.{v} R₀) :
    (PresheafOfModules.sheafification (restrictedRingMap J K H α)).obj
        ((PresheafOfModules.pushforward₀ H R₀).obj Q) ≅
      (SheafOfModules.pushforward (𝟙 (restrictedRing J K H R))).obj
        ((PresheafOfModules.sheafification α).obj Q) :=
  asIso (sheafificationRestrictionComparison J K H α Q)

end Sheafification

/-! ### Two invisible steps that are not structural identities -/

section Bridges

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- Restriction of scalars along an identity morphism of presheaves of rings is the identity. -/
theorem restrictScalars_id_obj (R : Cᵒᵖ ⥤ RingCat.{t}) (Q : PresheafOfModules.{v} R) :
    (PresheafOfModules.restrictScalars (𝟙 R)).obj Q = Q := rfl

/-- `PresheafOfModules.pushforward` along the identity morphism of presheaves of rings is the
bare precomposition functor `PresheafOfModules.pushforward₀`. -/
theorem pushforward_obj_eq_pushforward₀_obj (H : C ⥤ D) (R : Dᵒᵖ ⥤ RingCat.{t})
    (P : PresheafOfModules.{v} R) :
    (PresheafOfModules.pushforward (F := H) (𝟙 (H.op ⋙ R))).obj P =
      (PresheafOfModules.pushforward₀ H R).obj P := rfl

end Bridges

/-! ### The sectionwise powers commute with restriction on the nose -/

section Sectionwise

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (H : C ⥤ D)
  (O : Dᵒᵖ ⥤ CommRingCat.{w})
  (P : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat.{w}))

/-- **The presheaf of sectionwise symmetric powers commutes with restriction along a functor of
sites**, definitionally: it is defined section by section. This is the sectionwise half of
Tag 01CI for a restriction. -/
theorem pushforward₀_symmetricAlgebraPiece (n : ℤ) :
    symPowInt (O := H.op ⋙ O) n
        ((PresheafOfModules.pushforward₀ H (O ⋙ forget₂ _ RingCat.{w})).obj P) =
      (PresheafOfModules.pushforward₀ H (O ⋙ forget₂ _ RingCat.{w})).obj
        (symPowInt (O := O) n P) := rfl

/-- The tensor analogue of `pushforward₀_symmetricAlgebraPiece`. -/
theorem pushforward₀_tensorAlgebraPiece (n : ℤ) :
    tensorAlgebraPiece (O := H.op ⋙ O) n
        ((PresheafOfModules.pushforward₀ H (O ⋙ forget₂ _ RingCat.{w})).obj P) =
      (PresheafOfModules.pushforward₀ H (O ⋙ forget₂ _ RingCat.{w})).obj
        (tensorAlgebraPiece (O := O) n P) := rfl

end Sectionwise

/-! ### Tag 01CI for a restriction to a slice site -/

section Slice

open _root_.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (F : SheafOfModules.{w} (toRingCat J Osharp)) (Y : C)
  [(J.over Y).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [(J.over Y).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify (J.over Y) AddCommGrpCat.{w}]

/-- **Tag 01CI for the restriction to a slice site, degreewise.** The degree-`n` symmetric power
of the restriction of `F` to the slice site over `Y` is the restriction of the degree-`n`
symmetric power of `F`. -/
noncomputable def symmetricPieceOverIso (n : ℤ) :
    (sheafifiedSymmetricAlgebra (J.over Y) (Osharp := Osharp.over Y) (F.over Y)).piece n ≅
      ((sheafifiedSymmetricAlgebra J F).piece n).over Y :=
  eqToIso (congrArg (PresheafOfModules.sheafification
      (restrictedRingMap (J.over Y) J (Over.forget Y) (𝟙 (toRingCat J Osharp).obj))).obj
      (pushforward₀_symmetricAlgebraPiece (Over.forget Y) Osharp.obj F.val n)) ≪≫
    sheafificationRestrictionIso (J.over Y) J (Over.forget Y)
      (𝟙 (toRingCat J Osharp).obj) (symPowInt n F.val)

/-- The tensor analogue of `symmetricPieceOverIso`. -/
noncomputable def tensorPieceOverIso (n : ℤ) :
    (sheafifiedTensorAlgebra (J.over Y) (Osharp := Osharp.over Y) (F.over Y)).piece n ≅
      ((sheafifiedTensorAlgebra J F).piece n).over Y :=
  eqToIso (congrArg (PresheafOfModules.sheafification
      (restrictedRingMap (J.over Y) J (Over.forget Y) (𝟙 (toRingCat J Osharp).obj))).obj
      (pushforward₀_tensorAlgebraPiece (Over.forget Y) Osharp.obj F.val n)) ≪≫
    sheafificationRestrictionIso (J.over Y) J (Over.forget Y)
      (𝟙 (toRingCat J Osharp).obj) (tensorAlgebraPiece n F.val)

/-- **Quasi-coherence of `Symⁿ F` from presentations of the symmetric powers of its restrictions
to a cover.** With `symmetricPieceOverIso` the slice-restriction obligation of the sheaf-theoretic
clause (5) of Tag 01CK is discharged, and what is left is exactly a presentation of a symmetric
power over each member of the cover. -/
theorem isQuasicoherent_piece_of_presentations
    [∀ Z : C, (J.over Z).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [∀ Z : C, HasSheafify (J.over Z) AddCommGrpCat.{w}]
    [∀ Z : C, (J.over Z).WEqualsLocallyBijective AddCommGrpCat.{w}]
    {I : Type w} {X : I → C} (hX : J.CoversTop X) (n : ℤ)
    (pres : ∀ i, ((sheafifiedSymmetricAlgebra (J.over (X i))
      (Osharp := Osharp.over (X i)) (F.over (X i))).piece n).Presentation) :
    ((sheafifiedSymmetricAlgebra J F).piece n).IsQuasicoherent := by
  refine SheafOfModules.QuasicoherentData.isQuasicoherent
    { I := I, X := X, coversTop := hX, presentation := fun i => ?_ }
  have e := symmetricPieceOverIso J F (X i) n
  exact @SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _ e.hom e.isIso_hom (pres i)

end Slice

end Stacks.SliceAlgebra

end
