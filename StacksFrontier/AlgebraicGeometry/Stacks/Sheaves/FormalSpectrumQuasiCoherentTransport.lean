module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicFormalSpectrumStages
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticDegreeZeroSystem
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticDerivedLimit
public import StacksFrontier.CategoryTheory.Sites.Modules.UniverseLiftQC
public import StacksFrontier.RingTheory.Koszul.LiftedSheafAlgebras

/-!
# The sites of the proof of Stacks 0H0L

Let `A` be an adic topological `S`-algebra with ideal of definition `I` and `𝒳` the category
fibred in sets of `X = Spf(A)`. This file sets up the chaotic ringed sites through which the
proof of Stacks 0H0L passes, and the identifications between them:

* the small model `AsSmall 𝒳_{affine}` of the affine site, with its structure sheaf lifted to the
  universe of the modules, and the ring transport from `(𝒳_{affine}, O)` to it;
* the full subcategory `𝒞` of the stages `Spec(A/I^{n+1}) → X` in the small model, for which
  every object of `𝒳_{affine}` has a cofiltered category of arrows to `𝒞`;
* if the powers of `I` never stabilize, the identification of `(𝒞, O|_𝒞)` with the ringed site
  `(ℕ, (A/I^{n+1}))` of Section 24.35 (Tag 0GZG), as a ring transport.

## Main definitions

* `AlgebraicGeometry.FormalSpace.smallStructure`: the structure sheaf on the small model.
* `AlgebraicGeometry.FormalSpace.smallTransport`: the ring transport
  `𝒳_{affine} ≌ AsSmall 𝒳_{affine}`.
* `AlgebraicGeometry.FormalSpace.SmallIsStage`: the stages in the small model.
* `AlgebraicGeometry.FormalSpace.stageNatTransport`: the ring transport `𝒞 ≌ ℕ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t u

namespace AlgebraicGeometry.FormalSpace

attribute [-instance] CategoryTheory.catToReflQuiver

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {A : Type u} [CommRing A]
  [TopologicalSpace A] [IsTopologicalRing A] {I : Ideal A} (D : QuotientSystem B S hS A)

/-- The commutative-ring-valued structure presheaf of `𝒳_{affine}`. -/
abbrev affineCommStructure : (formalSpectrumAffine D)ᵒᵖ ⥤ CommRingCat.{u} :=
  Stack.affineStructureCommPresheaf B S hS (formalSpectrumProjection D)

/-- **The structure sheaf of the small model of `𝒳_{affine}`**, lifted to the universe
`max (u + 1) t` of the modules of `QC(𝒳)`. -/
def smallStructure :
    (AsSmall.{max (u + 1) t} (formalSpectrumAffine D))ᵒᵖ ⥤ CommRingCat.{max (u + 1) t} where
  obj Y := CommRingCat.of (ULift.{max (u + 1) t}
    ((affineCommStructure D).obj (op (AsSmall.down.obj Y.unop))))
  map f := CommRingCat.ofHom
    ((ULift.ringEquiv.{u, max (u + 1) t}).symm.toRingHom.comp
      (((affineCommStructure D).map (AsSmall.down.map f.unop).op).hom.comp
        (ULift.ringEquiv.{u, max (u + 1) t}).toRingHom))
  map_id Y := by
    ext x
    exact congrArg (fun φ => (CommRingCat.Hom.hom φ) x.down)
      ((affineCommStructure D).map_id (op (AsSmall.down.obj Y.unop)))
  map_comp f g := by
    ext x
    exact congrArg (fun φ => (CommRingCat.Hom.hom φ) x.down)
      ((affineCommStructure D).map_comp (AsSmall.down.map f.unop).op (AsSmall.down.map g.unop).op)

/-- **The ring transport from `(𝒳_{affine}, O)` to its small model**: the sections of the lifted
structure sheaf are the sections of `O`, lifted. -/
def smallTransport :
    Stacks.UniverseLift.RingTransport
      (AsSmall.equiv : formalSpectrumAffine D ≌ AsSmall.{max (u + 1) t} (formalSpectrumAffine D))
      (formalSpectrumAffineStructure D)
      (Stacks.ChaoticSite.systemRing
        (Stacks.ChaoticSite.degreeZeroDiagram (smallStructure.{t} D))) where
  iso _ := ULift.ringEquiv.{u, max (u + 1) t}
  naturality _ _ := rfl

variable (hA : TopologicalRing.IsAdic A) (hI : TopologicalRing.IsIdealOfDefinition I)

/-- **The stages `Spec(A/I^{n+1}) → X` in the small model** of `𝒳_{affine}`. -/
def SmallIsStage : ObjectProperty (AsSmall.{max (u + 1) t} (formalSpectrumAffine D)) :=
  fun Y => IsStage D hA hI (AsSmall.down.obj Y)

/-- In the small model of `𝒳_{affine}`, there is at most one arrow from any object to a stage. -/
theorem subsingleton_hom_smallStage (Y Z : AsSmall.{max (u + 1) t} (formalSpectrumAffine D))
    (hZ : SmallIsStage.{t} D hA hI Z) : Subsingleton (Y ⟶ Z) := by
  obtain ⟨n, hn⟩ := hZ
  refine ⟨fun f g => ULift.ext _ _ ?_⟩
  have : Subsingleton (AsSmall.down.obj Y ⟶ AsSmall.down.obj Z) := by
    rw [show AsSmall.down.obj Z = stage D hA hI n from hn]
    infer_instance
  exact @Subsingleton.elim _ this _ _

/-- **For every object `Y` of the small model, the arrows from `Y` to a stage form a cofiltered
category**. -/
instance isCofiltered_structuredArrow_smallIsStage
    (Y : AsSmall.{max (u + 1) t} (formalSpectrumAffine D)) :
    IsCofiltered (StructuredArrow Y (SmallIsStage.{t} D hA hI).ι) := by
  have hsub : ∀ X Z : StructuredArrow Y (SmallIsStage.{t} D hA hI).ι, Subsingleton (X ⟶ Z) := by
    intro X Z
    have := subsingleton_hom_smallStage D hA hI X.right.obj Z.right.obj Z.right.property
    exact ⟨fun f g => StructuredArrow.hom_ext _ _
      (ObjectProperty.hom_ext _ (@Subsingleton.elim _ this _ _))⟩
  have hle : ∀ (X Z : StructuredArrow Y (SmallIsStage.{t} D hA hI).ι) (a b : ℕ),
      AsSmall.down.obj X.right.obj = stage D hA hI a →
        AsSmall.down.obj Z.right.obj = stage D hA hI b → a ≤ b → Nonempty (X ⟶ Z) := by
    intro X Z a b ha hb hab
    have hmap : AsSmall.down.obj X.right.obj ⟶ AsSmall.down.obj Z.right.obj :=
      eqToHom ha ≫ stageHomOfLE D hA hI hab ≫ eqToHom hb.symm
    have := subsingleton_hom_smallStage D hA hI Y Z.right.obj Z.right.property
    exact ⟨StructuredArrow.homMk (ObjectProperty.homMk ⟨hmap⟩) (@Subsingleton.elim _ this _ _)⟩
  obtain ⟨n, ⟨f⟩⟩ := exists_hom_stage D hA hI (AsSmall.down.obj Y)
  have : Nonempty (StructuredArrow Y (SmallIsStage.{t} D hA hI).ι) :=
    ⟨StructuredArrow.mk (Y := (⟨AsSmall.up.obj (stage D hA hI n), n, rfl⟩ :
      (SmallIsStage.{t} D hA hI).FullSubcategory)) ⟨f⟩⟩
  refine { cone_objs := fun X Z ↦ ?_, cone_maps := fun X Z f g ↦ ?_ }
  · obtain ⟨a, ha⟩ := X.right.property
    obtain ⟨b, hb⟩ := Z.right.property
    rcases le_total a b with hab | hba
    · exact ⟨X, 𝟙 X, (hle X Z a b ha hb hab).some, trivial⟩
    · exact ⟨Z, (hle Z X b a hb ha hba).some, 𝟙 Z, trivial⟩
  · exact ⟨X, 𝟙 X, (hsub X Z).elim _ _⟩

/-- The stages of the small model are the stages of `𝒳_{affine}`. -/
def smallStageEquivalence :
    (SmallIsStage.{t} D hA hI).FullSubcategory ≌ (IsStage D hA hI).FullSubcategory where
  functor := ObjectProperty.lift _ ((SmallIsStage.{t} D hA hI).ι ⋙ AsSmall.down)
    (fun Y => Y.property)
  inverse := ObjectProperty.lift _ ((IsStage D hA hI).ι ⋙ AsSmall.up) (fun x => x.property)
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)

variable {hA hI} in
/-- **If the powers of `I` never stabilize, the stages of the small model form the ringed site
`ℕ`** of Section 24.35. -/
def smallStageNatEquivalence (hstrict : ∀ n : ℕ, I ^ (n + 1) ≠ I ^ (n + 2)) :
    (SmallIsStage.{t} D hA hI).FullSubcategory ≌ Stacks.LiftedNat.{max (u + 1) t} :=
  (smallStageEquivalence.{t} D hA hI).trans
    ((stageEquivalence D hA hI hstrict).symm.trans Stacks.LiftedNat.equivalence)

variable (I) in
/-- The ideal of definition, read in the lifted ring `ULift A`. -/
abbrev liftedIdeal : Ideal (ULift.{max (u + 1) t} A) :=
  I.map (ULift.ringEquiv.{u, max (u + 1) t} (R := A)).symm

omit [TopologicalSpace A] [IsTopologicalRing A] in
/-- The image of the power `I'^k` of the lifted ideal `I'` under `ULift A ≃+* A` is `I^k`. -/
theorem map_liftedIdeal_pow (k : ℕ) :
    (liftedIdeal.{t} I ^ k).map (ULift.ringEquiv.{u, max (u + 1) t} (R := A)) = I ^ k := by
  rw [Ideal.map_pow, liftedIdeal]
  congr 1
  exact Ideal.map_of_equiv (I := I) (ULift.ringEquiv.{u, max (u + 1) t} (R := A)).symm

/-- The ring isomorphism `ULift A ⧸ I'^{k+1} ≃+* O(Spec(A/I^{k+1}))`, lifted. -/
def stageNatRingEquiv (k : ℕ) :
    ULift.{max (u + 1) t} A ⧸ liftedIdeal.{t} I ^ (k + 1) ≃+*
      ULift.{max (u + 1) t} ((affineCommStructure D).obj (op (stage D hA hI k))) :=
  (Ideal.quotientEquiv (liftedIdeal.{t} I ^ (k + 1)) (I ^ (k + 1))
    (ULift.ringEquiv.{u, max (u + 1) t} (R := A)) (map_liftedIdeal_pow.{t} (k + 1)).symm).trans
    ((stageRingEquiv D hA hI k).symm.trans (ULift.ringEquiv.{u, max (u + 1) t}).symm)

/-- `stageNatRingEquiv` sends the class of `a` modulo `I'^{k+1}` to the lift of the image of the
class of `a` in `A/I^{k+1}`. -/
theorem stageNatRingEquiv_mk (k : ℕ) (a : ULift.{max (u + 1) t} A) :
    stageNatRingEquiv.{t} D hA hI k (Ideal.Quotient.mk _ a) =
      ULift.up ((stageRingEquiv D hA hI k).symm (Ideal.Quotient.mk _ a.down)) :=
  rfl

variable {hA hI} in
/-- **The ringed site of stages is the ringed site `(ℕ, (A/I^{n+1}))` of Section 24.35**
(Tag 0GZG), if the powers of `I` never stabilize: the identification of the stages with `ℕ`,
together with `O(Spec(A/I^{n+1})) = A/I^{n+1}`, as a ring transport onto the presheaf of rings
underlying the sheaf `𝒜` of Proposition 0GZK (for the lifted ring `ULift A`). -/
def stageNatTransport (hstrict : ∀ n : ℕ, I ^ (n + 1) ≠ I ^ (n + 2)) :
    Stacks.UniverseLift.RingTransport (smallStageNatEquivalence.{t} D hstrict)
      ((SmallIsStage.{t} D hA hI).ι.op ⋙
        Stacks.ChaoticSite.systemRing (Stacks.ChaoticSite.degreeZeroDiagram (smallStructure.{t} D)))
      (Stacks.ChaoticSite.systemRing (Stacks.LiftedNat.liftDiagram
        (Koszul.idealPowQuotientAlgebraDiagram (liftedIdeal.{t} I)))) where
  iso n := stageNatRingEquiv.{t} D hA hI n.unop.down
  naturality {n m} f x := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h : (unop m).down ≤ (unop n).down := Stacks.LiftedNat.down_le_down_iff.2 (leOfHom f.unop)
    have key := stageRingEquiv_map D hA hI h
      ((stageRingEquiv D hA hI (unop n).down).symm (Ideal.Quotient.mk _ a.down))
    rw [RingEquiv.apply_symm_apply, Ideal.Quotient.factor_mk] at key
    exact congrArg ULift.up ((RingEquiv.symm_apply_eq _).2 key.symm)

end AlgebraicGeometry.FormalSpace

end
