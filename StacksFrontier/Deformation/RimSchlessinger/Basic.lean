module

public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksFrontier.Deformation.Basic
public import StacksFrontier.Deformation.Cofibered
public import StacksFrontier.Deformation.Predeformation.Associated
public import StacksFrontier.Deformation.Predeformation.Basic
public import StacksFrontier.Deformation.Schlessinger.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Rim-Schlessinger condition and deformation categories

The Rim-Schlessinger condition (RS) asks that a category cofibered in groupoids take pushouts
along small extensions to fibre products. A deformation category is a predeformation category
satisfying (RS). Condition (RS) implies Schlessinger's conditions (S1) and (S2).

## Main definitions

* `SatisfiesRS`: condition (RS) for a functor to the category of Artinian local algebras with
  fixed residue field.
* `IsDeformationCategory`: a predeformation category over `𝒞_Λ` satisfying (RS).
* `IsDeformationFunctor`: a set-valued functor whose value at the residue field is a singleton and
  whose category of elements satisfies (RS).

## Main results

* `isLimit_of_map_isLimit`: under (RS), a pullback cone whose image is limiting is limiting, when
  the second morphism of the base cospan is surjective.
* `isDeformationCategory_iff`: a functor is a deformation functor exactly when its category of
  elements is a deformation category.
* `satisfiesRS_objectsOverFunctor`: the category localized at an object of the special fibre
  satisfies (RS).
* `isDeformationCategory_objectsOverFunctor`: the localized category is a deformation category.
* `schlessingerConditionS1_of_satisfiesRS`: (RS) implies (S1).
* `schlessingerConditionS2_of_satisfiesRS`: (RS) implies (S2).

## Implementation notes

That a fibre-product square lies over the fibre-product square of algebras is expressed by
requiring the image of the limiting pullback cone to be limiting.

## References

* [Stacks Project, Tag 06J2](https://stacks.math.columbia.edu/tag/06J2)
* [Stacks Project, Tag 06J3](https://stacks.math.columbia.edu/tag/06J3)
* [Stacks Project, Tag 06J7](https://stacks.math.columbia.edu/tag/06J7)
* [Stacks Project, Tag 06J9](https://stacks.math.columbia.edu/tag/06J9)
* [Stacks Project, Tag 06JA](https://stacks.math.columbia.edu/tag/06JA)
* [Stacks Project, Tag 06JC](https://stacks.math.columbia.edu/tag/06JC)
-/

@[expose] public section

namespace Deformation

/-! ### Condition (RS) for a category cofibered in groupoids -/

section
open CategoryTheory CategoryTheory.Limits
universe u v w u₁ v₁

/-- Condition (RS): every cospan over a cospan of Artinian local algebras whose second
morphism is surjective has a pullback cone which remains a pullback cone in the base. -/
@[stacks 06J2,
  sga "7 VI 2.5"]
public abbrev SatisfiesRS {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ
  k] {F : Type u₁} [Category.{v₁} F] (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) : Prop :=
    IsCofiberedInGroupoids p ∧ (∀ {x₁ x₂ x : F} (f₁ : x₁ ⟶ x) (f₂ : x₂ ⟶ x), Function.Surjective
      (p.map f₂).hom → ∃ c : PullbackCone f₁ f₂, (Nonempty (IsLimit c) ∧ Nonempty (IsLimit (c.map
        p))))

end

/-! ### Fibre squares for condition (RS) -/

section
open CategoryTheory CategoryTheory.Limits
universe u v w u₁ v₁

/-- Under condition (RS), a square over a pullback square is a pullback square when the
second morphism in the base cospan is surjective. -/
@[stacks 06J3]
public theorem isLimit_of_map_isLimit
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hp : SatisfiesRS p)
    {x₁ x₂ x : F} (f₁ : x₁ ⟶ x) (f₂ : x₂ ⟶ x)
    (c : PullbackCone f₁ f₂)
    (hsurj : Function.Surjective (p.map f₂).hom)
    (hc : Nonempty (IsLimit (c.map p))) :
    Nonempty (IsLimit c) := by
  obtain ⟨d, ⟨hd⟩, ⟨hdp⟩⟩ := hp.2 f₁ f₂ hsurj
  obtain ⟨hcp⟩ := hc
  let m : c.pt ⟶ d.pt := PullbackCone.IsLimit.lift hd c.fst c.snd c.condition
  have hm₁ : m ≫ d.fst = c.fst := PullbackCone.IsLimit.lift_fst hd c.fst c.snd c.condition
  have hm₂ : m ≫ d.snd = c.snd := PullbackCone.IsLimit.lift_snd hd c.fst c.snd c.condition
  let i := hcp.conePointUniqueUpToIso hdp
  have hm : p.map m = i.hom := by
    apply PullbackCone.IsLimit.hom_ext hdp
    · show p.map m ≫ p.map d.fst = i.hom ≫ p.map d.fst
      rw [← p.map_comp, hm₁]
      exact (hcp.conePointUniqueUpToIso_hom_comp hdp WalkingCospan.left).symm
    · show p.map m ≫ p.map d.snd = i.hom ≫ p.map d.snd
      rw [← p.map_comp, hm₂]
      exact (hcp.conePointUniqueUpToIso_hom_comp hdp WalkingCospan.right).symm
  have : IsIso (p.map m) := hm ▸ i.isIso_hom
  have : p.op.IsHomLift (p.map m).op m.op := by
    simpa using (Functor.IsHomLift.map m.op (p := p.op))
  have : p.op.IsStronglyCartesian (p.map m).op m.op := hp.1.isStronglyCartesian_homLift _ _
  have : IsIso m.op := Functor.IsStronglyCartesian.isIso_of_base_isIso p.op (p.map m).op m.op
  have : IsIso m := isIso_of_op m
  exact ⟨IsLimit.ofIsoLimit hd (PullbackCone.ext (asIso m) hm₁.symm hm₂.symm).symm⟩

end

/-! ### Deformation categories -/

section
open CategoryTheory
universe u v w u₁ v₁

/-- A predeformation category over `𝒞_Λ` satisfying condition (RS). -/
@[stacks 06J9 "objects"]
structure IsDeformationCategory {Λ : Type u} {k : Type w} [CommRing Λ] [Field k]
    [Algebra Λ k] {F : Type u₁} [Category.{v₁} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k) : Prop where
  /-- The category over `𝒞_Λ` is a predeformation category. -/
  predeformation : IsPredeformationCategory p
  /-- The category over `𝒞_Λ` satisfies condition (RS). -/
  satisfiesRS : SatisfiesRS p

add_to_stacks 06J9 "morphisms" BasedFunctor

end

/-! ### Deformation functors -/

section
open CategoryTheory
universe u v w t

/-- A set-valued functor is a deformation functor if its value at the residue
field is a singleton and its associated cofibered set satisfies (RS). -/
@[stacks 06JA "deformation_functor"]
public abbrev IsDeformationFunctor
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (F : ArtinianLocalAlgCat.{u, max v w, w} Λ k ⥤ Type t) : Prop :=
  IsPredeformationFunctor F ∧
    SatisfiesRS (CategoryOfElements.π F)

/-- A functor is a deformation functor exactly when its associated cofibered set
is a deformation category. -/
@[stacks 06JA "deformation_functor"]
public theorem isDeformationCategory_iff
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (F : ArtinianLocalAlgCat.{u, max v w, w} Λ k ⥤ Type t) :
    IsDeformationCategory (CategoryOfElements.π F) ↔
      IsDeformationFunctor F := ⟨fun h => ⟨(isPredeformationCategory_iff F).mp h.predeformation,
        h.satisfiesRS⟩, fun ⟨h₁, h₂⟩ => ⟨(isPredeformationCategory_iff F).mpr h₁, h₂⟩⟩

end

/-! ### The associated functor of a deformation category is a predeformation functor -/

section

add_to_stacks 06JA "associated_predeformation" isPredeformationFunctor_isomorphismClasses

end

/-! ### Rim–Schlessinger condition for a localized deformation category -/

section
open CategoryTheory CategoryTheory.Limits
universe u v w v₁ u₁

/-- The category localized at an object of the special fibre inherits the
Rim–Schlessinger condition. -/
@[stacks 06JC "Rim-Schlessinger condition"]
public theorem satisfiesRS_objectsOverFunctor
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : SatisfiesRS p)
    (x : p.Fiber (residueFieldObject.{u, v, w} Λ k)) :
    SatisfiesRS
      (objectsOverFunctor p x.1) := by
  let q := objectsOverFunctor p x.1
  refine ⟨(isPredeformationCategory_objectsOverFunctor p hp.1 x).cofibered, ?_⟩
  intro A B C f₁ f₂ hsurj
  change Function.Surjective (p.map f₂.left).hom at hsurj
  obtain ⟨c, ⟨hc, hcp⟩⟩ := hp.2 f₁.left f₂.left hsurj
  obtain ⟨hc⟩ := hc
  obtain ⟨hcp⟩ := hcp
  let D : Over x.1 := Over.mk (c.fst ≫ A.hom)
  let toF (s : PullbackCone f₁ f₂) : PullbackCone f₁.left f₂.left :=
    PullbackCone.mk s.fst.left s.snd.left
      (by simpa using congrArg (fun g => g.left) s.condition)
  let d : PullbackCone f₁ f₂ :=
    PullbackCone.mk
      (Over.homMk (U := D) c.fst rfl)
      (Over.homMk c.snd (by
        show c.snd ≫ B.hom = c.fst ≫ A.hom
        rw [← Over.w f₂, ← Over.w f₁, ← Category.assoc, ← c.condition, Category.assoc]))
      (Over.OverMorphism.ext c.condition)
  refine ⟨d, ⟨?_, ?_⟩⟩
  · refine ⟨PullbackCone.isLimitAux d
      (fun s => Over.homMk (U := s.pt) (V := D) (hc.lift (toF s)) (by
        show hc.lift (toF s) ≫ (c.fst ≫ A.hom) = s.pt.hom
        rw [← Category.assoc, hc.fac (toF s) WalkingCospan.left]
        exact s.fst.w))
      (fun s => Over.OverMorphism.ext (hc.fac (toF s) WalkingCospan.left))
      (fun s => Over.OverMorphism.ext (hc.fac (toF s) WalkingCospan.right))
      (by
        intro s m hm
        apply Over.OverMorphism.ext
        apply PullbackCone.IsLimit.hom_ext hc
        · have h := congrArg (fun g => g.left) (hm WalkingCospan.left)
          change m.left ≫ c.fst = s.fst.left at h
          exact h.trans (hc.fac (toF s) WalkingCospan.left).symm
        · have h := congrArg (fun g => g.left) (hm WalkingCospan.right)
          change m.left ≫ c.snd = s.snd.left at h
          exact h.trans (hc.fac (toF s) WalkingCospan.right).symm)⟩
  · refine ⟨?_⟩
    have hi : d.map q ≅ c.map p :=
      PullbackCone.ext (Iso.refl _)
        (by
          show q.map d.fst = 𝟙 (q.obj d.pt) ≫ p.map c.fst
          rw [objectsOverFunctor_map]
          show p.map c.fst = 𝟙 (p.obj c.pt) ≫ p.map c.fst
          rw [Category.id_comp])
        (by
          show q.map d.snd = 𝟙 (q.obj d.pt) ≫ p.map c.snd
          rw [objectsOverFunctor_map]
          show p.map c.snd = 𝟙 (p.obj c.pt) ≫ p.map c.snd
          rw [Category.id_comp])
    exact IsLimit.ofIsoLimit hcp hi

/-- The category localized at an object of the special fibre is a deformation
category when the original category satisfies the Rim–Schlessinger condition. -/
@[stacks 06JC "deformation category"]
public theorem isDeformationCategory_objectsOverFunctor
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : SatisfiesRS p)
    (x : p.Fiber (residueFieldObject.{u, v, w} Λ k)) :
    IsDeformationCategory
      (objectsOverFunctor p x.1) :=
  ⟨isPredeformationCategory_objectsOverFunctor p hp.1 x, satisfiesRS_objectsOverFunctor p hp x⟩

end

/-! ### Condition (RS) implies Schlessinger's conditions (S1) and (S2) -/

section
open CategoryTheory
open CategoryTheory.Limits
universe u v w u₁ v₁



/-- Condition (RS) implies Schlessinger's condition (S1). -/
@[stacks 06J7 "condition (S1)"]
public theorem schlessingerConditionS1_of_satisfiesRS
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hp : SatisfiesRS p) :
    SchlessingerConditionS1 p := by
  rcases hp with ⟨hp, hrs⟩
  refine ⟨?_⟩
  intro x₁ x₂ x f₁ f₂ hsurj A₁₂ g₁ g₂ hPB
  obtain ⟨c, hc, hcp⟩ := hrs f₁ f₂ hsurj
  let d := hPB.cone.flip
  let hc' : IsLimit d := PullbackCone.flipIsLimit hPB.isLimit
  let α : p.obj c.pt ≅ A₁₂ := hcp.some.conePointUniqueUpToIso hc'
  obtain ⟨y, φ, hφ⟩ := exists_pushforward hp α.hom c.pt rfl
  let : p.IsHomLift α.hom φ := hφ
  let : Functor.IsStronglyCocartesian p α.hom φ :=
    isStronglyCocartesian_of_isCofiberedInGroupoids hp α.hom φ hφ
  let : IsIso α.hom := by infer_instance
  let : IsIso φ := Functor.IsStronglyCocartesian.isIso_of_base_isIso p α.hom φ
  let heq : p.obj y = A₁₂ := IsHomLift.codomain_eq p α.hom φ
  have hmapφ : p.map φ = α.hom ≫ eqToHom heq.symm := by
    apply (cancel_mono (eqToHom heq)).mp
    simpa [heq] using (IsHomLift.fac p α.hom φ).symm
  have hmapInv : p.map (inv φ) = eqToHom heq ≫ α.inv := by
    simp [hmapφ]
  have hαfirst : α.hom ≫ g₁ = p.map c.fst := by
    show (hcp.some.conePointUniqueUpToIso hc').hom ≫ g₁ = p.map c.fst
    simpa [d] using hcp.some.conePointUniqueUpToIso_hom_comp hc' WalkingCospan.left
  have hαsecond : α.hom ≫ g₂ = p.map c.snd := by
    show (hcp.some.conePointUniqueUpToIso hc').hom ≫ g₂ = p.map c.snd
    simpa [d] using hcp.some.conePointUniqueUpToIso_hom_comp hc' WalkingCospan.right
  have hfirst : α.inv ≫ p.map c.fst = g₁ := (Iso.inv_comp_eq α).2 hαfirst.symm
  have hsecond : α.inv ≫ p.map c.snd = g₂ := (Iso.inv_comp_eq α).2 hαsecond.symm
  refine ⟨⟨y, heq, inv φ ≫ c.fst, inv φ ≫ c.snd, ?_, ?_, ?_⟩⟩
  · rw [Category.assoc, Category.assoc]
    exact congrArg (fun q => inv φ ≫ q) c.condition.symm
  · rw [Functor.map_comp, hmapInv, Category.assoc, hfirst]
  · rw [Functor.map_comp, hmapInv, Category.assoc, hsecond]

private noncomputable def pullbackCompletion_map_isLimit
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    {x₁ x₂ x : F} (f₁ : x₁ ⟶ x) (f₂ : x₂ ⟶ x)
    {A₁₂ : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (g₁ : A₁₂ ⟶ p.obj x₁) (g₂ : A₁₂ ⟶ p.obj x₂)
    (hPB : IsPullback g₂ g₁ (p.map f₂) (p.map f₁))
    (P : PullbackCompletion p f₁ f₂ g₁ g₂) :
    IsLimit ((PullbackCone.mk P.toFirst P.toSecond P.comm.symm).map p) := by
  have hmapPB : IsPullback (p.map P.toFirst) (p.map P.toSecond)
      (p.map f₁) (p.map f₂) :=
    hPB.flip.of_iso' (eqToIso P.apex_eq) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simpa using P.map_toFirst.symm)
      (by simpa using P.map_toSecond.symm)
      (by simp) (by simp)
  change IsLimit (PullbackCone.mk (p.map P.toFirst) (p.map P.toSecond) ?_)
  exact hmapPB.isLimit

/-- A dual-number projection `Aε ⟶ A₀` is surjective. -/
public lemma surjective_of_isDualNumberProjection
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {Aε A₀ : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (e : Aε ⟶ A₀) (he : IsDualNumberProjection e) :
    Function.Surjective e.hom := by
  rcases (isDualNumberProjection_iff e).mp he with ⟨i₀, iε, he⟩
  intro y
  obtain ⟨z, hz⟩ := TrivSqZeroExt.fst_surjective (R := k) (M := k) (i₀ y)
  obtain ⟨x, hx⟩ := iε.surjective z
  refine ⟨x, i₀.injective ?_⟩
  simpa [hx, hz] using congrArg (fun q : Aε →ₐ[Λ] k => q x) he

/-- Condition (RS) implies Schlessinger's condition (S2). -/
@[stacks 06J7 "condition (S2)"]
public theorem schlessingerConditionS2_of_satisfiesRS
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hp : SatisfiesRS p) :
    SchlessingerConditionS2 p := by
  refine ⟨?_, ?_⟩
  · intro x xε x₀ d e hdual Aε g gε hPB
    exact (schlessingerConditionS1_of_satisfiesRS hp).completion
      d e (surjective_of_isDualNumberProjection _ hdual) g gε hPB
  · intro x xε x₀ d e hdual Aε g gε hPB P Q
    let cQ : PullbackCone d e := PullbackCone.mk Q.toFirst Q.toSecond Q.comm.symm
    have hmapQ := pullbackCompletion_map_isLimit d e g gε hPB Q
    let hQ := (isLimit_of_map_isLimit hp d e cQ
      (surjective_of_isDualNumberProjection _ hdual) ⟨hmapQ⟩).some
    let b : P.apex ⟶ Q.apex :=
      PullbackCone.IsLimit.lift hQ P.toFirst P.toSecond P.comm.symm
    have hbfirst : b ≫ Q.toFirst = P.toFirst :=
      PullbackCone.IsLimit.lift_fst hQ P.toFirst P.toSecond P.comm.symm
    have hbsecond : b ≫ Q.toSecond = P.toSecond :=
      PullbackCone.IsLimit.lift_snd hQ P.toFirst P.toSecond P.comm.symm
    have hbase : p.map b = eqToHom P.apex_eq ≫ eqToHom Q.apex_eq.symm := by
      apply PullbackCone.IsLimit.hom_ext hmapQ
      · show p.map b ≫ p.map Q.toFirst =
          (eqToHom P.apex_eq ≫ eqToHom Q.apex_eq.symm) ≫ p.map Q.toFirst
        rw [← Functor.map_comp, hbfirst, P.map_toFirst, Q.map_toFirst]
        simp
      · show p.map b ≫ p.map Q.toSecond =
          (eqToHom P.apex_eq ≫ eqToHom Q.apex_eq.symm) ≫ p.map Q.toSecond
        rw [← Functor.map_comp, hbsecond, P.map_toSecond, Q.map_toSecond]
        simp
    exact ⟨b, by simpa using hbfirst.symm, hbase⟩

end

end Deformation
