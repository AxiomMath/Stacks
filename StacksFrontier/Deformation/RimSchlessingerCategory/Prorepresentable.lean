module

public import StacksFrontier.Deformation.BaseCategory.FibreProduct
public import StacksFrontier.Deformation.Groupoid.BaseCategory
public import StacksFrontier.Deformation.RimSchlessinger.Basic
public import StacksFrontier.Deformation.RimSchlessingerCategory.ElementsCofibered

/-!
# Prorepresentable functors are deformation functors

The functor represented on Artinian local algebras by a complete local algebra has one element
over the residue field and satisfies the (RS) pullback condition. Consequently, every
prorepresentable functor is a deformation functor.

## Main results

* `Deformation.restrictedCoyoneda_isPredeformationFunctor` gives the singleton value at `k`.
* `Deformation.restrictedCoyoneda_satisfiesRS` gives the (RS) property.
* `Deformation.isDeformationFunctor_of_isProrepresentable` gives the resulting implication.

## Implementation notes

The represented functor is the restricted covariant Yoneda functor. The singleton condition
expresses the uniqueness of a compatible map from the representing algebra to `k`; (RS)
expresses the universal property of its pullback hom-sets, using the concrete fibre product of
Artinian local algebras along a surjection.

## References

* [Stacks Project, Tag 06JB](https://stacks.math.columbia.edu/tag/06JB)
-/

@[expose] public section

namespace Deformation

section
open CategoryTheory CategoryTheory.Limits

universe u v w

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- **Stacks Project, Tag 06JB.** A functor represented by a complete local algebra takes the
residue-field object to a one-element set. -/
@[stacks 06JB "singleton value at the residue field"]
theorem restrictedCoyoneda_isPredeformationFunctor
    (R : CompleteLocalAlgCat.{u, max v w, w} Λ k) :
    IsPredeformationFunctor (restrictedCoyoneda R) := by
  show Nonempty (Unique ((restrictedCoyoneda R).obj (residueFieldObject Λ k)))
  refine ⟨{ default := residuePoint R, uniq := ?_ }⟩
  intro f
  apply CompleteLocalAlgCat.Hom.ext
  ext x
  have hf := f.residue_comm x
  have hdefault := (residuePoint R).residue_comm x
  rw [completeResidueFieldObject_residue] at hf hdefault
  exact (ULift.algEquiv.{u, w, v} (R := Λ) (A := k)).injective (hf.trans hdefault.symm)

/-- A pullback cone in a category of elements is limiting if its image in the base is limiting and
every factorisation of a cone through it in the base is compatible with the elements. -/
private theorem isLimit_of_map_isLimit_elements {C : Type*} [Category C] {F : C ⥤ Type*}
    {x₁ x₂ x : F.Elements} {f₁ : x₁ ⟶ x} {f₂ : x₂ ⟶ x} (c : PullbackCone f₁ f₂)
    (hc : IsLimit (c.map (CategoryOfElements.π F)))
    (hlift : ∀ (s : PullbackCone f₁ f₂) (l : s.pt.1 ⟶ c.pt.1), l ≫ c.fst.val = s.fst.val →
      l ≫ c.snd.val = s.snd.val → F.map l s.pt.2 = c.pt.2) :
    Nonempty (IsLimit c) := by
  let l (s : PullbackCone f₁ f₂) : s.pt.1 ⟶ c.pt.1 :=
    PullbackCone.IsLimit.lift hc s.fst.val s.snd.val (congrArg (fun q => q.val) s.condition)
  have l_fst (s : PullbackCone f₁ f₂) : l s ≫ c.fst.val = s.fst.val :=
    PullbackCone.IsLimit.lift_fst hc _ _ _
  have l_snd (s : PullbackCone f₁ f₂) : l s ≫ c.snd.val = s.snd.val :=
    PullbackCone.IsLimit.lift_snd hc _ _ _
  refine ⟨PullbackCone.isLimitAux c
    (fun s => CategoryOfElements.homMk s.pt c.pt (l s) (hlift s _ (l_fst s) (l_snd s)))
    (fun s => CategoryOfElements.ext _ _ _ (l_fst s))
    (fun s => CategoryOfElements.ext _ _ _ (l_snd s)) fun s m hm => ?_⟩
  exact CategoryOfElements.ext _ _ _ <| PullbackCone.IsLimit.hom_ext hc
    ((congrArg (fun q => q.val) (hm WalkingCospan.left)).trans (l_fst s).symm)
    ((congrArg (fun q => q.val) (hm WalkingCospan.right)).trans (l_snd s).symm)

/-- **Stacks Project, Tag 06JB.** A functor represented by a complete local algebra satisfies
(RS), since maps out of the representing object preserve the relevant fibre products. -/
@[stacks 06JB "the (RS) property"]
theorem restrictedCoyoneda_satisfiesRS
    (R : CompleteLocalAlgCat.{u, max v w, w} Λ k) :
    SatisfiesRS (CategoryOfElements.π (restrictedCoyoneda R)) := by
  refine ⟨isCofiberedInGroupoids_elementsProjection _, ?_⟩
  intro x₁ x₂ x f₁ f₂ hf₂
  let f₁' := f₁.val
  let f₂' := f₂.val
  let h : ArtinianLocalAlgCat.IsConcretePullback f₁' f₂' :=
    (ArtinianLocalAlgCat.hasPullback_of_surjective f₁' f₂' (Or.inr hf₂)).1
  have h₁ : (artinianToComplete.map f₁').hom.comp x₁.2.hom = x.2.hom := by
    simpa [f₁', restrictedCoyoneda_map_hom] using congrArg CompleteLocalAlgCat.Hom.hom f₁.property
  have h₂ : (artinianToComplete.map f₂').hom.comp x₂.2.hom = x.2.hom := by
    simpa [f₂', restrictedCoyoneda_map_hom] using congrArg CompleteLocalAlgCat.Hom.hom f₂.property
  have hcompat : f₁'.hom.comp x₁.2.hom = f₂'.hom.comp x₂.2.hom := h₁.trans h₂.symm
  let pair : R.carrier →ₐ[Λ] x₁.1.carrier × x₂.1.carrier :=
    AlgHom.prod x₁.2.hom x₂.2.hom
  have hmem (z : R.carrier) : pair z ∈ AlgHom.pullback f₁'.hom f₂'.hom :=
    DFunLike.congr_fun hcompat z
  let gAlg : R.carrier →ₐ[Λ] AlgHom.pullback f₁'.hom f₂'.hom :=
    pair.codRestrict (AlgHom.pullback f₁'.hom f₂'.hom) hmem
  have hfst : h.fst.hom.comp gAlg = x₁.2.hom := by
    rw [ArtinianLocalAlgCat.IsConcretePullback.fst_hom]
    exact AlgHom.ext fun _ => rfl
  have hsnd : h.snd.hom.comp gAlg = x₂.2.hom := by
    rw [ArtinianLocalAlgCat.IsConcretePullback.snd_hom]
    exact AlgHom.ext fun _ => rfl
  let g : R ⟶ artinianToComplete.obj h.obj :=
    { hom := gAlg
      isLocal := by
        constructor
        intro z hz
        have hz₁ : IsUnit (x₁.2.hom z) := by
          have hu := hz.map h.fst.hom.toRingHom
          change IsUnit ((h.fst.hom.comp gAlg) z) at hu
          rw [hfst] at hu
          exact hu
        let : IsLocalHom x₁.2.hom.toRingHom := x₁.2.isLocal
        exact IsLocalHom.map_nonunit z hz₁
      residue_comm := by
        intro z
        calc
          (artinianToComplete.obj h.obj).residueEquiv
              (IsLocalRing.residue (artinianToComplete.obj h.obj) (gAlg z)) =
            ArtinianLocalAlgCat.pullbackToResidueField f₁' f₂' (gAlg z) :=
              h.residueEquiv_residue (gAlg z)
          _ = x₁.1.residueEquiv (IsLocalRing.residue x₁.1 (x₁.2.hom z)) := by
            show x.fst.residueEquiv
                (IsLocalRing.residue x.fst (f₁'.hom ((gAlg z).val.1))) = _
            have hcoord : (gAlg z).val.1 = x₁.2.hom z := rfl
            rw [hcoord]
            exact f₁'.residue_comm (x₁.2.hom z)
          _ = R.residueEquiv (IsLocalRing.residue R z) := x₁.2.residue_comm z }
  let y : (restrictedCoyoneda R).Elements := (restrictedCoyoneda R).elementsMk h.obj g
  have hg₁ : (restrictedCoyoneda R).map h.fst g = x₁.2 := CompleteLocalAlgCat.Hom.ext hfst
  have hg₂ : (restrictedCoyoneda R).map h.snd g = x₂.2 := CompleteLocalAlgCat.Hom.ext hsnd
  let m₁ : y ⟶ x₁ := CategoryOfElements.homMk y x₁ h.fst hg₁
  let m₂ : y ⟶ x₂ := CategoryOfElements.homMk y x₂ h.snd hg₂
  have hbase : h.fst ≫ f₁' = h.snd ≫ f₂' := h.isPullback.w
  let c : PullbackCone f₁ f₂ := PullbackCone.mk m₁ m₂ (CategoryOfElements.ext _ _ _ hbase)
  have hcone : c.map (CategoryOfElements.π (restrictedCoyoneda R)) ≅
      PullbackCone.mk h.fst h.snd hbase :=
    PullbackCone.ext (Iso.refl _) (by rfl) (by rfl)
  have hext (a b : (restrictedCoyoneda R).obj h.obj)
      (h₁ : (restrictedCoyoneda R).map h.fst a = (restrictedCoyoneda R).map h.fst b)
      (h₂ : (restrictedCoyoneda R).map h.snd a = (restrictedCoyoneda R).map h.snd b) : a = b := by
    refine CompleteLocalAlgCat.Hom.ext (AlgHom.ext fun z => Subtype.ext (Prod.ext ?_ ?_))
    · have e := congrArg CompleteLocalAlgCat.Hom.hom h₁
      simp only [restrictedCoyoneda_map_hom, ArtinianLocalAlgCat.IsConcretePullback.fst_hom] at e
      exact DFunLike.congr_fun e z
    · have e := congrArg CompleteLocalAlgCat.Hom.hom h₂
      simp only [restrictedCoyoneda_map_hom, ArtinianLocalAlgCat.IsConcretePullback.snd_hom] at e
      exact DFunLike.congr_fun e z
  have hlim := IsLimit.ofIsoLimit h.isPullback.isLimit hcone.symm
  refine ⟨c, isLimit_of_map_isLimit_elements c hlim fun s l hl₁ hl₂ => hext _ _ ?_ ?_, ⟨hlim⟩⟩
  · change _ = (restrictedCoyoneda R).map h.fst g
    rw [hg₁]
    exact (congrArg (fun q => (restrictedCoyoneda R).map q s.pt.2)
      (show l ≫ h.fst = s.fst.val from hl₁)).trans s.fst.property
  · change _ = (restrictedCoyoneda R).map h.snd g
    rw [hg₂]
    exact (congrArg (fun q => (restrictedCoyoneda R).map q s.pt.2)
      (show l ≫ h.snd = s.snd.val from hl₂)).trans s.snd.property

/-- Condition (RS) for a set-valued functor is invariant under natural isomorphism. -/
theorem satisfiesRS_of_natIso
    {F G : ArtinianLocalAlgCat.{u, max v w, w} Λ k ⥤ Type (max v w)} (e : F ≅ G)
    (hG : SatisfiesRS (CategoryOfElements.π G)) :
    SatisfiesRS (CategoryOfElements.π F) := by
  refine ⟨isCofiberedInGroupoids_elementsProjection _, ?_⟩
  intro x₁ x₂ x f₁ f₂ hf₂
  let E := CategoryOfElements.map e.hom
  obtain ⟨cG, ⟨hcG⟩, ⟨hcpG⟩⟩ := hG.2 (E.map f₁) (E.map f₂) hf₂
  let y : F.Elements := F.elementsMk cG.pt.1 (e.inv.app cG.pt.1 cG.pt.2)
  have hy {z : F.Elements} (q : cG.pt ⟶ E.obj z) : F.map q.val y.2 = z.2 := by
    apply natIso_app_injective e z.1
    calc
      e.hom.app z.1 (F.map q.val y.2) = G.map q.val (e.hom.app cG.pt.1 y.2) :=
        e.hom.naturality_apply q.val y.2
      _ = G.map q.val cG.pt.2 := by simp [y]
      _ = e.hom.app z.1 z.2 := q.property
  let m₁ : y ⟶ x₁ := CategoryOfElements.homMk y x₁ cG.fst.val (hy cG.fst)
  let m₂ : y ⟶ x₂ := CategoryOfElements.homMk y x₂ cG.snd.val (hy cG.snd)
  let c : PullbackCone f₁ f₂ := PullbackCone.mk m₁ m₂
    (CategoryOfElements.ext _ _ _ (congrArg (fun q : cG.pt ⟶ E.obj x => q.val) cG.condition))
  let sG (s : PullbackCone f₁ f₂) : PullbackCone (E.map f₁) (E.map f₂) :=
    PullbackCone.mk (E.map s.fst) (E.map s.snd) (by simp only [← Functor.map_comp, s.condition])
  have hcone : c.map (CategoryOfElements.π F) ≅ cG.map (CategoryOfElements.π G) :=
    PullbackCone.ext (Iso.refl _) (by rfl) (by rfl)
  have hlim := hcpG.ofIsoLimit hcone.symm
  refine ⟨c, isLimit_of_map_isLimit_elements c hlim ?_, ⟨hlim⟩⟩
  intro s l hl₁ hl₂
  have hl : l = (hcG.lift (sG s)).val :=
    PullbackCone.IsLimit.hom_ext hcpG
      (hl₁.trans (congrArg (fun q : (sG s).pt ⟶ E.obj x₁ => q.val)
        (hcG.fac (sG s) WalkingCospan.left)).symm)
      (hl₂.trans (congrArg (fun q : (sG s).pt ⟶ E.obj x₂ => q.val)
        (hcG.fac (sG s) WalkingCospan.right)).symm)
  subst hl
  apply natIso_app_injective e y.1
  calc
    e.hom.app y.1 (F.map (hcG.lift (sG s)).val s.pt.2) =
        G.map (hcG.lift (sG s)).val (e.hom.app s.pt.1 s.pt.2) :=
          e.hom.naturality_apply _ s.pt.2
    _ = cG.pt.2 := (hcG.lift (sG s)).property
    _ = e.hom.app y.1 y.2 := by simp [y]

/-- **Stacks Project, Tag 06JB.** Every prorepresentable functor on Artinian local algebras is
a deformation functor. -/
@[stacks 06JB "prorepresentable implies deformation"]
theorem isDeformationFunctor_of_isProrepresentable
    (F : ArtinianLocalAlgCat.{u, max v w, w} Λ k ⥤ Type (max v w))
    (hF : IsProrepresentable F) :
    IsDeformationFunctor F := by
  obtain ⟨R, ⟨e⟩⟩ := hF
  show IsPredeformationFunctor F ∧ SatisfiesRS (CategoryOfElements.π F)
  obtain ⟨u⟩ := restrictedCoyoneda_isPredeformationFunctor R
  refine ⟨?_, satisfiesRS_of_natIso e (restrictedCoyoneda_satisfiesRS R)⟩
  show Nonempty (Unique (F.obj (residueFieldObject Λ k)))
  refine ⟨{ default := e.inv.app (residueFieldObject Λ k) u.default, uniq := ?_ }⟩
  intro a
  apply natIso_app_injective e (residueFieldObject Λ k)
  calc
    e.hom.app (residueFieldObject Λ k) a = u.default := u.uniq _
    _ = e.hom.app (residueFieldObject Λ k)
        (e.inv.app (residueFieldObject Λ k) u.default) := by simp

end

end Deformation
