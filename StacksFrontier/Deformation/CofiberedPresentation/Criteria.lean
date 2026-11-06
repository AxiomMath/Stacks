module

public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.Deformation.Examples.Linear.ContinuousRepresentationsDenseRestriction
public import StacksFrontier.Deformation.CofiberedPresentation.Existence
public import StacksFrontier.Deformation.CofiberedPresentation.MinimalPresentation
public import StacksFrontier.Deformation.CofiberedPresentation.MinimalUniqueness
public import StacksFrontier.Deformation.GroupoidQuotient.InfinitesimalAutomorphisms
public import StacksFrontier.Deformation.GroupoidQuotient.Minimality
public import StacksFrontier.Deformation.Schlessinger.MiniversalSeparable

/-!
# Criteria for a smooth prorepresentable presentation

The four conditions on a category cofibered in groupoids `ℱ` over `𝒞_Λ` that the source
compares: `ℱ` admits a presentation by a normalized, by an arbitrary, or by a minimal smooth
prorepresentable groupoid in functors on `𝒞_Λ`, and `ℱ` is a deformation category whose
tangent space and whose space of infinitesimal automorphisms are finite dimensional over `k`.

Conditions (2), (3) and (4) are equivalent and are implied by (1); when the residue field
carries no nonzero `Λ`-derivation — in particular when `k` is separable over the image field
of `Λ` — all four are equivalent. The minimal smooth prorepresentable groupoids in functors
presenting `ℱ` are unique up to isomorphism.

## Main definitions

* `Deformation.HasNormalizedPresentation`, `Deformation.HasSmoothPresentation`,
  `Deformation.HasMinimalPresentation` and
  `Deformation.IsFiniteDimensionalDeformationCategory` are the four conditions.

## Main results

* `Deformation.isCofiberedInGroupoids_of_equivalenceOver`: being cofibered in groupoids
  transports along an equivalence over the base.
* `Deformation.hasMinimalPresentation_of_hasNormalizedPresentation`: (1) implies (3).
* `Deformation.hasSmoothPresentation_of_hasMinimalPresentation`: (3) implies (2).
* `Deformation.hasMinimalPresentation_of_isFiniteDimensionalDeformationCategory`:
  (4) implies (3).
* `Deformation.isFiniteDimensionalDeformationCategory_of_hasSmoothPresentation`: (2) implies
  (4), the direction of Tag 06L8 that reads the three conditions off a presentation.
* `Deformation.hasSmoothPresentation_iff_isFiniteDimensionalDeformationCategory`:
  **Stacks Project, Tag 06L8**, the equivalence of (2) and (4).
* `Deformation.hasNormalizedPresentation_iff_hasMinimalPresentation`: (1) and (3) are
  equivalent when the residue field carries no nonzero `Λ`-derivation, and
  `Deformation.hasNormalizedPresentation_iff_hasMinimalPresentation_of_isSeparable` is the
  same statement under separability of `k` over the image field of `Λ`.
* `Deformation.hasSmoothPresentation_tfae`: the equivalence of (2), (3) and (4).
* `Deformation.tfae_of_isSeparable`: the equivalence of all four conditions when `k` is
  separable over the image field of `Λ`.

## Implementation notes

The hom-set universe of `ℱ` is the universe `v` that also measures the values of the
groupoids in functors. This is the common specialisation of the three inputs: Tag 06L2
produces a minimal presentation of a category whose hom-set universe enters the values of
the groupoid, and Tag 06L3 is available at `GroupoidInFunctors.IsMinimal.{u, v, w, v}`.

The implication (2) implies (4) reads the three conditions off the presentation `[U/R] → ℱ`.
`ℱ` is cofibered in groupoids because the quotient is and the presentation is an equivalence
over `𝒞_Λ`; it is a deformation category by part (1) of Tag 06KU; its tangent space is
finite-dimensional because the differential of the quotient morphism `U → [U/R]` is
surjective, which is part (2) of Tag 06KU, and `TU` is finite-dimensional by Schlessinger's
theorem, Tag 06JM, for the prorepresentable `U`; and its infinitesimal automorphisms are
finite-dimensional because part (3) of Tag 06KU embeds `Inf([U/R])` into `TR`. The last
transport is through the tangent space at the identity of the automorphism functor, which is
independent of the point of the special fibre and of the choice of pushforwards by part (2)
of Tag 06JV, and which Tag 07W6 carries along the presentation.

Vanishing of `Der_Λ(k, k)` is the input to the equivalence of (1) with the other three. It is
taken as a hypothesis in `Deformation.hasNormalizedPresentation_iff_hasMinimalPresentation`,
which is the form the proof uses, and is supplied from separability of `k` over the image
field of `Λ` by `Deformation.derivation_eq_zero_of_residueImageField_separable`.

## References

* [Stacks Project, Tag 06TE](https://stacks.math.columbia.edu/tag/06TE)
* [Stacks Project, Tag 06JV](https://stacks.math.columbia.edu/tag/06JV)
* [Stacks Project, Tag 06KN](https://stacks.math.columbia.edu/tag/06KN)
* [Stacks Project, Tag 06KU](https://stacks.math.columbia.edu/tag/06KU)
* [Stacks Project, Tag 06L2](https://stacks.math.columbia.edu/tag/06L2)
* [Stacks Project, Tag 06L3](https://stacks.math.columbia.edu/tag/06L3)
* [Stacks Project, Tag 06L8](https://stacks.math.columbia.edu/tag/06L8)
* [Stacks Project, Tag 07W6](https://stacks.math.columbia.edu/tag/07W6)
-/

@[expose] public section

namespace Deformation

/-! ### The four conditions -/

section
open CategoryTheory

universe u v w u₁

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {ℱ : Type u₁} [Category.{v} ℱ] (p : ℱ ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)

/-- Condition (1): `ℱ` admits a presentation by a normalized smooth prorepresentable groupoid
in functors on `𝒞_Λ`. -/
def HasNormalizedPresentation : Prop :=
  ∃ G : GroupoidInFunctors.{_, max v w, max v w} (ArtinianLocalAlgCat.{u, max v w, w} Λ k),
    GroupoidInFunctors.IsNormalized.{u, v, w} G ∧ GroupoidInFunctors.IsSmooth G ∧
      GroupoidInFunctors.IsProrepresentable G ∧ Nonempty (Presentation G p)

/-- Condition (2): `ℱ` admits a presentation by a smooth prorepresentable groupoid in functors
on `𝒞_Λ`. -/
def HasSmoothPresentation : Prop :=
  ∃ G : GroupoidInFunctors.{_, max v w, max v w} (ArtinianLocalAlgCat.{u, max v w, w} Λ k),
    GroupoidInFunctors.IsSmooth G ∧ GroupoidInFunctors.IsProrepresentable G ∧
      Nonempty (Presentation G p)

/-- Condition (3): `ℱ` admits a presentation by a minimal smooth prorepresentable groupoid
in functors on `𝒞_Λ`. -/
def HasMinimalPresentation : Prop :=
  ∃ G : GroupoidInFunctors.{_, max v w, max v w} (ArtinianLocalAlgCat.{u, max v w, w} Λ k),
    GroupoidInFunctors.IsMinimal.{u, v, w, v} G ∧ GroupoidInFunctors.IsSmooth G ∧
      GroupoidInFunctors.IsProrepresentable G ∧ Nonempty (Presentation G p)

/-- Condition (4): `ℱ` is a deformation category whose tangent space and whose space of
infinitesimal automorphisms are finite dimensional over `k`. -/
def IsFiniteDimensionalDeformationCategory : Prop :=
  ∃ hp : IsDeformationCategory.{u, v, w} p,
    (let _ : Fact (IsPredeformationCategory.{u, v, w} (BasedCategory.ofFunctor p).p) :=
      ⟨hp.predeformation⟩
    let _ : Fact (SchlessingerConditionS2 (CategoryOfElements.π
      (isomorphismClasses (BasedCategory.ofFunctor p) hp.predeformation.cofibered))) :=
      ⟨tangentConditionS2.{u, v, w} hp⟩
    FiniteDimensional k (tangentSpaceArtinian.{u, w, v} Λ k
      (isomorphismClasses (BasedCategory.ofFunctor p) hp.predeformation.cofibered))) ∧
    ∀ (x : ℱ), p.obj x = residueFieldObject.{u, v, w} Λ k →
      ∀ PF : ChosenPushforwardsAt p x, FiniteDimensional k
        ↥((infinitesimalAutomorphismLinearLift.{u, v, w} PF hp.satisfiesRS).functor.obj
          (FGModuleCat.of k (ULift.{v} k)))

end

/-! ### Transport along an equivalence over the base -/

section
open CategoryTheory CategoryTheory.Functor

universe v₂ u₂ v₃ u₃ v₄ u₄

variable {𝒞 : Type u₂} [Category.{v₂} 𝒞] {𝒮 : Type u₃} [Category.{v₃} 𝒮]
  {𝒯 : Type u₄} [Category.{v₄} 𝒯] {P : 𝒮 ⥤ 𝒞} {Q : 𝒯 ⥤ 𝒞}

/-- Pushforwards transport along an equivalence over the base: push the image of the object
downstairs, carry the resulting arrow back up, and correct by the counit, which is vertical. -/
private theorem exists_pushforward_of_equivalenceOver
    (e : StacksRepresentableCFG.EquivalenceOver (𝒞 := 𝒞) P Q)
    (hP : IsCofiberedInGroupoids P) {A B : 𝒞} (g : A ⟶ B) (t : 𝒯) (ht : Q.obj t = A) :
    ∃ (t' : 𝒯) (ψ : t ⟶ t'), Q.IsHomLift g ψ := by
  subst ht
  obtain ⟨s', φ, hφ⟩ := exists_pushforward hP g (e.inv.functor.obj t)
    (Functor.congr_obj e.inv.w t)
  let _ := hφ
  have h₁ : Q.IsHomLift g (e.hom.functor.map φ) :=
    Functor.isHomLift_map_of_comp_eq e.hom.w g φ
  have h₂ : Q.IsHomLift (𝟙 (Q.obj t)) (e.counitIso.hom.app t) :=
    e.isHomLift_counitIso_hom_app t
  let _ := h₂
  have h₃ : Q.IsHomLift (𝟙 (Q.obj t)) (CategoryTheory.inv (e.counitIso.hom.app t)) :=
    IsHomLift.lift_id_inv_isIso Q (Q.obj t) (e.counitIso.hom.app t)
  let _ := h₁
  let _ := h₃
  refine ⟨e.hom.functor.obj s',
    CategoryTheory.inv (e.counitIso.hom.app t) ≫ e.hom.functor.map φ, ?_⟩
  simpa using IsHomLift.comp Q (𝟙 (Q.obj t)) g
    (CategoryTheory.inv (e.counitIso.hom.app t)) (e.hom.functor.map φ)

/-- Descent of an arrow along a cocartesian one transports along an equivalence over the base:
the fill-in is produced downstairs, where the comparison functor commutes strictly with the
two structure functors, and is pulled back through the fully faithful comparison. -/
private theorem existsUnique_descent_of_equivalenceOver
    (e : StacksRepresentableCFG.EquivalenceOver (𝒞 := 𝒞) P Q)
    (hP : IsCofiberedInGroupoids P) {a b c : 𝒯} (α : a ⟶ b) (β : a ⟶ c)
    (h : Q.obj b ⟶ Q.obj c) (hh : Q.map α ≫ h = Q.map β) :
    ∃! χ : b ⟶ c, Q.map χ = h ∧ α ≫ χ = β := by
  set Ψ := e.inv.functor
  have ff : Ψ.FullyFaithful := e.toEquivalence.symm.fullyFaithfulFunctor
  have eb : P.obj (Ψ.obj b) = Q.obj b := Functor.congr_obj e.inv.w b
  have ec : P.obj (Ψ.obj c) = Q.obj c := Functor.congr_obj e.inv.w c
  set h' : P.obj (Ψ.obj b) ⟶ P.obj (Ψ.obj c) := eqToHom eb ≫ h ≫ eqToHom ec.symm with hh'
  have hmap : ∀ {x y : 𝒯} (f : x ⟶ y),
      P.map (Ψ.map f) = eqToHom (Functor.congr_obj e.inv.w x) ≫ Q.map f ≫
        eqToHom (Functor.congr_obj e.inv.w y).symm := fun f => Functor.congr_hom e.inv.w f
  have hfac : P.map (Ψ.map β) = P.map (Ψ.map α) ≫ h' := by
    rw [hmap α, hmap β, hh']
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [← Category.assoc (Q.map α) h, hh]
  let _ : P.IsHomLift (P.map (Ψ.map α)) (Ψ.map α) := IsHomLift.map P (Ψ.map α)
  let _ : P.IsStronglyCocartesian (P.map (Ψ.map α)) (Ψ.map α) :=
    isStronglyCocartesian_of_isCofiberedInGroupoids hP _ _ inferInstance
  let _ : P.IsHomLift (P.map (Ψ.map β)) (Ψ.map β) := IsHomLift.map P (Ψ.map β)
  obtain ⟨χ', ⟨hχ'lift, hχ'fac⟩, huniq⟩ :=
    Functor.IsStronglyCocartesian.universal_property P (P.map (Ψ.map α)) (Ψ.map α)
      h' (P.map (Ψ.map β)) hfac (Ψ.map β)
  let _ := hχ'lift
  have hχ'eq : P.map χ' = h' := by
    simpa using IsHomLift.fac' P h' χ'
  refine ⟨ff.preimage χ', ⟨?_, ?_⟩, ?_⟩
  · have h1 := hmap (ff.preimage χ')
    rw [ff.map_preimage, hχ'eq, hh'] at h1
    exact ((cancel_mono (eqToHom ec.symm)).mp ((cancel_epi (eqToHom eb)).mp h1)).symm
  · apply ff.map_injective
    rw [Ψ.map_comp, ff.map_preimage, hχ'fac]
  · rintro χ₁ ⟨hχ₁, hχ₂⟩
    apply ff.map_injective
    rw [ff.map_preimage]
    have hlift : P.IsHomLift h' (Ψ.map χ₁) := by
      refine IsHomLift.of_fac' P h' (Ψ.map χ₁) rfl rfl ?_
      rw [hmap χ₁, hχ₁, hh']
      simp
    exact huniq (Ψ.map χ₁) ⟨hlift, by rw [← Ψ.map_comp, hχ₂]⟩

/-- **Being cofibered in groupoids transports along an equivalence over the base.** This is the
cofibered counterpart of
`StacksRepresentableCFG.isFiberedInGroupoids_of_equivalenceOver`, and the direction a
presentation needs: the quotient of a groupoid in functors is cofibered in groupoids, and an
equivalence over `𝒞_Λ` out of it carries that to the presented category. Neither half of the
conclusion is formal, the fibres of a functor being cut out by an equality in the base: an
equivalence over the base is only essentially surjective, and both halves are recovered
because the comparison commutes strictly with the structure functors and the counit is
vertical. -/
theorem isCofiberedInGroupoids_of_equivalenceOver
    (e : StacksRepresentableCFG.EquivalenceOver (𝒞 := 𝒞) P Q)
    (hP : IsCofiberedInGroupoids P) : IsCofiberedInGroupoids Q where
  exists_lift := by
    intro V U f x hx
    obtain ⟨t', ψ, hψ⟩ := exists_pushforward_of_equivalenceOver e hP f.unop x.unop
      (congrArg Opposite.unop hx)
    exact ⟨Opposite.op t', ψ.op, isHomLift_op Q f.unop ψ (inst := hψ)⟩
  unique_lift := by
    intro x y z φ ψ f hf
    obtain ⟨χ, ⟨hχ1, hχ2⟩, huniq⟩ := existsUnique_descent_of_equivalenceOver e hP
      φ.unop ψ.unop f.unop (by simpa using congrArg Quiver.Hom.unop hf)
    refine ⟨χ.op, ⟨?_, ?_⟩, ?_⟩
    · exact Quiver.Hom.unop_inj hχ1
    · exact Quiver.Hom.unop_inj (by simpa using hχ2)
    · rintro χ₁ ⟨h1, h2⟩
      refine Quiver.Hom.unop_inj (huniq χ₁.unop ⟨?_, ?_⟩)
      · exact congrArg Quiver.Hom.unop h1
      · simpa using congrArg Quiver.Hom.unop h2

end

/-! ### Comparison of the four conditions -/

section
open CategoryTheory

universe u v w u₁

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {ℱ : Type u₁} [Category.{v} ℱ] (p : ℱ ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)

/-- A normalized smooth prorepresentable presentation is minimal: the differential of its
quotient morphism is bijective by part (1) of Tag 06KN, so the kernel of that differential is
the single tangent vector attached to the zero derivation, and part (2) of Tag 06KN applies. -/
theorem hasMinimalPresentation_of_hasNormalizedPresentation [IsNoetherianRing Λ]
    [Module.Finite Λ k] (h : HasNormalizedPresentation.{u, v, w} p) :
    HasMinimalPresentation.{u, v, w} p := by
  obtain ⟨G, hnorm, hsmooth, hpro, hpres⟩ := h
  refine ⟨G, ?_, hsmooth, hpro, hpres⟩
  refine (GroupoidInFunctors.isMinimal_iff_quotientDifferential_ker_le_derivationRange.{u, v, w}
    G hpro hsmooth).2 (fun x hx => ?_)
  exact ⟨0, ((GroupoidInFunctors.isNormalized_iff_bijective_quotientDifferential.{u, v, w}
    G).1 hnorm).1 hx |>.symm⟩

/-- A minimal smooth prorepresentable presentation is in particular a smooth prorepresentable
presentation. -/
theorem hasSmoothPresentation_of_hasMinimalPresentation
    (h : HasMinimalPresentation.{u, v, w} p) : HasSmoothPresentation.{u, v, w} p := by
  obtain ⟨G, -, hsmooth, hpro, hpres⟩ := h
  exact ⟨G, hsmooth, hpro, hpres⟩

/-- A deformation category with finite-dimensional tangent space and finite-dimensional
infinitesimal automorphisms has a minimal smooth prorepresentable presentation: this is
Tag 06L2, whose minimal presentation is read as an equivalence over `𝒞_Λ` out of the quotient
by `Deformation.presentationOfQuotientEquivalence`. -/
theorem hasMinimalPresentation_of_isFiniteDimensionalDeformationCategory [IsNoetherianRing Λ]
    [Module.Finite Λ k] (h : IsFiniteDimensionalDeformationCategory.{u, v, w} p) :
    HasMinimalPresentation.{u, v, w} p := by
  obtain ⟨hp, hT, hInf⟩ := h
  let hpre := hp.predeformation
  let _ : Fact (IsPredeformationCategory.{u, v, w} (BasedCategory.ofFunctor p).p) := ⟨hpre⟩
  let _ : Fact (SchlessingerConditionS2 (CategoryOfElements.π
    (isomorphismClasses (BasedCategory.ofFunctor p) hpre.cofibered))) :=
    ⟨tangentConditionS2.{u, v, w} hp⟩
  let _ : FiniteDimensional k (tangentSpaceArtinian.{u, w, v} Λ k
    (isomorphismClasses (BasedCategory.ofFunctor p) hpre.cofibered)) := hT
  obtain ⟨Q⟩ := exists_minimalPresentation.{u, v, w, u₁, v} p hp
    hInf
  let U := restrictedCoyoneda.{u, max v w, w} Q.ξ.base
  let f := (associatedMorphism hpre.cofibered Q.ξ Q.pushforwards).toBasedFunctor
  let P := presentationGroupoid p U f.toFunctor f.w hpre.cofibered
  refine ⟨P.toGroupoidInFunctors, Q.minimal, Q.smooth, Q.prorepresentable, ?_⟩
  let pm := presentationMorphism p U f.toFunctor f.w P
  have hpm : pm.1.IsEquivalence := Q.quotientEquivalence
  let _ : pm.1.Full := presentationMorphism_full p U f.toFunctor f.w P hpre.cofibered
  let _ : pm.1.Faithful := presentationMorphism_faithful p U f.toFunctor f.w P
  let _ : pm.1.EssSurj := hpm.essSurj
  exact ⟨presentationOfQuotientEquivalence P.toGroupoidInFunctors p pm.1 pm.2.1⟩

/-- The tangent module at the rank-one module of a prorepresentable functor, viewed as a
deformation category over `𝒞_Λ`, is finite-dimensional, by Schlessinger's theorem. -/
private theorem finiteDimensional_tangentModuleAt_of_isProrepresentable [IsNoetherianRing Λ]
    [Module.Finite Λ k] (F : ArtinianLocalAlgCat.{u, max v w, w} Λ k ⥤ Type (max v w))
    (hF : IsProrepresentable F) (hπ : IsDeformationCategory.{u, v, w} (CategoryOfElements.π F)) :
    FiniteDimensional k ↥(tangentModuleAt.{u, v, w}
      (BasedCategory.ofFunctor (CategoryOfElements.π F)) hπ
      (FGModuleCat.of k (ULift.{v} k))) := by
  obtain ⟨_, hfin, -⟩ := (isProrepresentable_iff_isDeformationFunctor.{u, v, w} F).mp hF
  let _ : Fact (IsPredeformationCategory.{u, v, w}
      (BasedCategory.ofFunctor (CategoryOfElements.π F)).p) := ⟨hπ.predeformation⟩
  let _ : Fact (SchlessingerConditionS2 (CategoryOfElements.π (isomorphismClasses
      (BasedCategory.ofFunctor (CategoryOfElements.π F)) hπ.predeformation.cofibered))) :=
    ⟨tangentConditionS2.{u, v, w} hπ⟩
  let _ := hfin
  exact (associatedTangentSpaceCarrierLinearEquiv.{u, v, w}
    (BasedCategory.ofFunctor (CategoryOfElements.π F)) hπ.predeformation
    (tangentConditionS2.{u, v, w} hπ)).symm.finiteDimensional

/-- **The tangent space of the quotient of a smooth prorepresentable groupoid in functors is
finite-dimensional.** The differential of the quotient morphism `U → [U/R]` is surjective,
every object of a strict fibre of the quotient being the image of an object of `U` over the
same algebra, and the tangent space of `U` is finite-dimensional by Schlessinger's theorem,
Tag 06JM, applied to the prorepresentable `U`. Surjectivity is the content of part (2) of
Tag 06KU that the finite-dimensionality needs; the full identification of `T[U/R]` with the
cokernel of `ds - dt` is `Deformation.quotientTangentEquiv`. -/
@[sga "7 VI 2.17" "partial"]
private theorem finiteDimensional_tangentModuleAt_quotient [IsNoetherianRing Λ]
    [Module.Finite Λ k]
    (G : GroupoidInFunctors.{_, max v w, max v w} (ArtinianLocalAlgCat.{u, max v w, w} Λ k))
    (hpro : GroupoidInFunctors.IsProrepresentable G)
    (hQ : IsDeformationCategory.{u, v, w} (Grothendieck.forget (evaluationFunctor G))) :
    FiniteDimensional k ↥(tangentModuleAt.{u, v, w}
      (BasedCategory.ofFunctor (Grothendieck.forget (evaluationFunctor G))) hQ
      (FGModuleCat.of k (ULift.{v} k))) := by
  have hπU : IsDeformationCategory.{u, v, w} (CategoryOfElements.π G.objects) :=
    objectsBasedDeformationCategory G
      (GroupoidInFunctors.isDeformationFunctor_objects_of_isProrepresentable.{u, v, w} G hpro)
  have hTU := finiteDimensional_tangentModuleAt_of_isProrepresentable.{u, v, w} G.objects
    ((GroupoidInFunctors.isProrepresentable_iff_objects_arrows G).1 hpro).1 hπU
  have hsurj : Function.Surjective (tangentMapAt.{u, v, w} hπU hQ (quotientBasedFunctor G)
      (FGModuleCat.of k (ULift.{v} k))) := by
    intro t
    obtain ⟨X, rfl⟩ := tangentClassAt_surjective.{u, v, w} _ hQ _ t
    obtain ⟨x, rfl⟩ := quotientFiberObject_surjective G _ X
    exact ⟨tangentClassAt.{u, v, w} _ hπU _ (objectFiber _ x),
      tangentMapAt_tangentClassAt.{u, v, w} hπU hQ (quotientBasedFunctor G) _
        (objectFiber _ x)⟩
  exact Module.Finite.of_surjective (hM := hTU) _ hsurj

/-- **The infinitesimal automorphisms of a category cofibered in groupoids with a smooth
prorepresentable presentation are finite-dimensional**, at every object of the special fibre
and for every choice of pushforwards there.

Part (3) of Tag 06KU embeds `Inf([U/R])` into the tangent space of the arrow functor `R`,
which is finite-dimensional by Schlessinger's theorem for the prorepresentable `R`. That
bounds the infinitesimal automorphisms of the quotient at one point and one choice of
pushforwards; the general case follows because the tangent space at the identity of the
automorphism functor, which Tag 06IA identifies with the infinitesimal automorphisms at the
rank-one module, is independent of both by part (2) of Tag 06JV, and because the `k`-linear map
it induces along the presentation, Tag 07W6, is injective — the presentation is faithful and
the comparison of dual-number pushforwards is vertical, hence invertible. -/
@[sga "7 VI 2.17" "partial"]
private theorem finiteDimensional_infinitesimalAutomorphisms_of_presentation
    [IsNoetherianRing Λ] [Module.Finite Λ k]
    (G : GroupoidInFunctors.{_, max v w, max v w} (ArtinianLocalAlgCat.{u, max v w, w} Λ k))
    (hG : GroupoidInFunctors.IsSmooth G)
    (hpro : GroupoidInFunctors.IsProrepresentable G)
    (hUdef : IsDeformationFunctor.{u, v, w} G.objects)
    (hRdef : IsDeformationFunctor.{u, v, w} G.arrows)
    (e : Presentation G p) (hp : IsDeformationCategory.{u, v, w} p)
    (x : ℱ) (hx : p.obj x = residueFieldObject.{u, v, w} Λ k)
    (PF : ChosenPushforwardsAt p x) :
    FiniteDimensional k
      ↥((infinitesimalAutomorphismLinearLift.{u, v, w} PF hp.satisfiesRS).functor.obj
        (FGModuleCat.of k (ULift.{v} k))) := by
  have hQ : IsDeformationCategory.{u, v, w} (Grothendieck.forget (evaluationFunctor G)) :=
    quotient_isDeformationCategory.{u, v, w, max v w} G hG hUdef hRdef
  let _ : e.inv.functor.Full := CategoryTheory.Equivalence.full_functor e.toEquivalence.symm
  let _ : e.inv.functor.Faithful :=
    CategoryTheory.Equivalence.faithful_functor e.toEquivalence.symm
  have hTR := finiteDimensional_tangentModuleAt_of_isProrepresentable.{u, v, w} G.arrows
    ((GroupoidInFunctors.isProrepresentable_iff_objects_arrows G).1 hpro).2
    (arrowsBasedDeformationCategory G hRdef)
  let _ : FiniteDimensional k ↥(tangentModuleAt.{u, v, w}
      (BasedCategory.ofFunctor (Functor.Elements.π G.arrows))
      (arrowsBasedDeformationCategory G hRdef)
      (FGModuleCat.of k (ULift.{v} k))) := hTR
  obtain ⟨hu₀⟩ := hUdef.1
  let y₀ : G.objects.Elements :=
    G.objects.elementsMk (residueFieldObject.{u, v, w} Λ k) hu₀.default
  let PF₀ : ChosenPushforwardsAt (Grothendieck.forget (evaluationFunctor G))
      ((quotientMorphism G).obj y₀) :=
    chosenPushforwardsAtOfCofibered hQ.predeformation.cofibered _
  have hInf₀ : FiniteDimensional k
      ↥((infinitesimalAutomorphismLinearLift.{u, v, w} PF₀ hQ.satisfiesRS).functor.obj
        (FGModuleCat.of k (ULift.{v} k))) :=
    Module.Finite.of_injective _ (quotientInfinitesimalBoundary_exact.{u, v, w, max v w}
      G hG hUdef hRdef PF₀ (FGModuleCat.of k (ULift.{v} k))).1
  have hxb : (Grothendieck.forget (evaluationFunctor G)).obj (e.inv.functor.obj x) =
      residueFieldObject.{u, v, w} Λ k := (Functor.congr_obj e.inv.w x).trans hx
  let Qx : ChosenPushforwardsAt (Grothendieck.forget (evaluationFunctor G))
      (e.inv.functor.obj x) :=
    chosenPushforwardsAtOfCofibered hQ.predeformation.cofibered _
  obtain ⟨jiso, -⟩ := existsUnique_pointIso.{u, v, w} hQ.predeformation
    (⟨e.inv.functor.obj x, hxb⟩ : (Grothendieck.forget (evaluationFunctor G)).Fiber
      (residueFieldObject.{u, v, w} Λ k)) ⟨(quotientMorphism G).obj y₀, rfl⟩
  let _ := naturalLocalizedTangentAddCommGroup PF₀ hQ.satisfiesRS
  let _ := naturalLocalizedTangentModule PF₀ hQ.satisfiesRS
  let _ := naturalLocalizedTangentAddCommGroup Qx hQ.satisfiesRS
  let _ := naturalLocalizedTangentModule Qx hQ.satisfiesRS
  let _ := naturalLocalizedTangentAddCommGroup PF hp.satisfiesRS
  let _ := naturalLocalizedTangentModule PF hp.satisfiesRS
  let _ := hInf₀
  let _ : FiniteDimensional k (localizedAutomorphismFunctorTangent PF₀) :=
    (tangentCarrierLinearEquiv.{u, v, w} PF₀ hQ.satisfiesRS).finiteDimensional
  have hLocx : FiniteDimensional k (localizedAutomorphismFunctorTangent Qx) :=
    (canonicalLocalizedTangentAutomorphismLinearEquiv.{u, v, w} hQ.satisfiesRS
      jiso.hom.val rfl Qx PF₀).symm.finiteDimensional
  obtain ⟨T, H, hHlift, -, hconj⟩ := exists_inducedInfinitesimalLinearMap.{u, v, w, u₁, v, _, _}
    e.inv.functor e.inv.w hp.satisfiesRS hQ.satisfiesRS PF Qx
  let _ : IsIso H := isIso_of_isHomLift_id hQ.predeformation.cofibered H hHlift
  have hTinj : Function.Injective T := by
    intro a b hab
    apply (localizedTangentEquivKernel PF).injective
    apply Subtype.ext
    apply Aut.ext
    apply Iso.ext
    apply Functor.Fiber.hom_ext
    apply e.inv.functor.map_injective
    have h1 := hconj a
    rw [hab] at h1
    exact (cancel_epi H).mp (h1.symm.trans (hconj b))
  let _ := hLocx
  let _ : FiniteDimensional k (localizedAutomorphismFunctorTangent PF) :=
    Module.Finite.of_injective T hTinj
  exact (tangentCarrierLinearEquiv.{u, v, w} PF hp.satisfiesRS).symm.finiteDimensional

/-- **Stacks Project, Tag 06L8**, the direction that reads the three conditions off a
presentation. A category cofibered in groupoids over `𝒞_Λ` which admits a presentation by a
smooth prorepresentable groupoid in functors is a deformation category whose tangent space and
whose space of infinitesimal automorphisms are finite dimensional over `k`.

The proof of the source, which is parts (1), (2) and (3) of Tag 06KU for the quotient together
with transport along the presentation. A prorepresentable groupoid in functors is a groupoid in
deformation functors by Example 06JB, so the quotient is a deformation category by part (1);
`ℱ` is cofibered in groupoids because the quotient is and a presentation is an equivalence over
`𝒞_Λ`, and is then a deformation category because condition (RS) and the special fibre
transport. The tangent space of the quotient is finite-dimensional by part (2), and the tangent
module transports because a presentation is an equivalence on every strict fibre. The
infinitesimal automorphisms are finite-dimensional by part (3). -/
@[sga "7 VI 2.17" "(1)"]
theorem isFiniteDimensionalDeformationCategory_of_hasSmoothPresentation [IsNoetherianRing Λ]
    [Module.Finite Λ k] (h : HasSmoothPresentation.{u, v, w} p) :
    IsFiniteDimensionalDeformationCategory.{u, v, w} p := by
  obtain ⟨G, hG, hpro, ⟨e⟩⟩ := h
  have hUdef : IsDeformationFunctor.{u, v, w} G.objects :=
    GroupoidInFunctors.isDeformationFunctor_objects_of_isProrepresentable.{u, v, w} G hpro
  have hRdef : IsDeformationFunctor.{u, v, w} G.arrows :=
    GroupoidInFunctors.isDeformationFunctor_arrows_of_isProrepresentable.{u, v, w} G hpro
  have hQ : IsDeformationCategory.{u, v, w} (Grothendieck.forget (evaluationFunctor G)) :=
    quotient_isDeformationCategory.{u, v, w, max v w} G hG hUdef hRdef
  let _ : e.inv.functor.Full := CategoryTheory.Equivalence.full_functor e.toEquivalence.symm
  let _ : e.inv.functor.Faithful :=
    CategoryTheory.Equivalence.faithful_functor e.toEquivalence.symm
  let _ : e.inv.functor.EssSurj :=
    CategoryTheory.Equivalence.essSurj_functor e.toEquivalence.symm
  have hcof : IsCofiberedInGroupoids p :=
    isCofiberedInGroupoids_of_equivalenceOver e hQ.predeformation.cofibered
  have hne : Nonempty (p.Fiber (residueFieldObject.{u, v, w} Λ k)) := by
    obtain ⟨E⟩ := hQ.predeformation.specialFiber
    exact ⟨⟨e.hom.functor.obj (E.inverse.obj ⟨PUnit.unit⟩).1,
      (Functor.congr_obj e.hom.w _).trans (E.inverse.obj ⟨PUnit.unit⟩).2⟩⟩
  have hp : IsDeformationCategory.{u, v, w} p := by
    have h₁ : IsCofiberedInGroupoids
        (e.inv.functor ⋙ Grothendieck.forget (evaluationFunctor G)) := by rwa [e.inv.w]
    have h₂ : Nonempty ((e.inv.functor ⋙ Grothendieck.forget (evaluationFunctor G)).Fiber
        (residueFieldObject.{u, v, w} Λ k)) := by rwa [e.inv.w]
    have h₃ := Deformation.Examples.isDeformationCategory_comp_of_essSurj.{u, v, w}
      e.inv.functor (Grothendieck.forget (evaluationFunctor G)) h₁ h₂ hQ
    rwa [e.inv.w] at h₃
  refine ⟨hp, ?_, fun x hx PF =>
    finiteDimensional_infinitesimalAutomorphisms_of_presentation p G hG hpro hUdef hRdef e hp
      x hx PF⟩
  let φ : BasedCategory.ofFunctor p ⥤ᵇ
      BasedCategory.ofFunctor (Grothendieck.forget (evaluationFunctor G)) :=
    ⟨e.inv.functor, e.inv.w⟩
  let _ : φ.toFunctor.Full := inferInstanceAs e.inv.functor.Full
  let _ : φ.toFunctor.Faithful := inferInstanceAs e.inv.functor.Faithful
  let _ : φ.toFunctor.EssSurj := inferInstanceAs e.inv.functor.EssSurj
  have hTp : FiniteDimensional k ↥(tangentModuleAt.{u, v, w} (BasedCategory.ofFunctor p) hp
      (FGModuleCat.of k (ULift.{v} k))) :=
    finiteDimensional_tangentModuleAt_of_fiberEquivalence.{u, v, w} hp hQ φ _
      (Deformation.full_fiberFunctor φ _) (Deformation.faithful_fiberFunctor φ _)
      (essSurj_fiberFunctor hcof φ _)
      (finiteDimensional_tangentModuleAt_quotient G hpro hQ)
  let _ : Fact (IsPredeformationCategory.{u, v, w} (BasedCategory.ofFunctor p).p) :=
    ⟨hp.predeformation⟩
  let _ : Fact (SchlessingerConditionS2 (CategoryOfElements.π
    (isomorphismClasses (BasedCategory.ofFunctor p) hp.predeformation.cofibered))) :=
    ⟨tangentConditionS2.{u, v, w} hp⟩
  let _ := hTp
  exact (associatedTangentSpaceCarrierLinearEquiv.{u, v, w} (BasedCategory.ofFunctor p)
    hp.predeformation (tangentConditionS2.{u, v, w} hp)).finiteDimensional

/-- **Stacks Project, Tag 06L8.** Let `ℱ` be a category cofibered in groupoids over `𝒞_Λ`.
Then `ℱ` admits a presentation by a smooth prorepresentable groupoid in functors on `𝒞_Λ` if
and only if `ℱ` is a deformation category, `dim_k Tℱ` is finite and `dim_k Inf(ℱ)` is finite.

The direction from the three conditions to a presentation is Tag 06L2, whose minimal
presentation is in particular a smooth prorepresentable one; the converse is
`Deformation.isFiniteDimensionalDeformationCategory_of_hasSmoothPresentation`, which is parts
(1), (2) and (3) of Tag 06KU transported along the presentation. Being cofibered in groupoids
is not a hypothesis here: it is part of condition (1) on one side and a consequence of the
presentation on the other. -/
@[stacks 06L8 "the tag in full: ℱ admits a presentation by a smooth prorepresentable groupoid \
in functors on 𝒞_Λ iff (1) ℱ is a deformation category, (2) dim_k Tℱ is finite and \
(3) dim_k Inf(ℱ) is finite. Both directions, at the general universes of the chapter: ℱ has \
hom-set universe v and the base is ArtinianLocalAlgCat.{u, max v w, w}, with no universe \
equation imposed. The standing hypothesis of the source that ℱ be cofibered in groupoids is \
not carried: it is part of condition (1) on one side, and on the other it is derived from the \
presentation by Deformation.isCofiberedInGroupoids_of_equivalenceOver. The forward direction \
goes through Stacks 06L2 rather than through the construction of Stacks 06L8 itself, which \
Deformation.exists_isSmooth_isProrepresentable_presentation carries at the restricted \
universe", sga "7 VI 2.12" "more general"]
theorem hasSmoothPresentation_iff_isFiniteDimensionalDeformationCategory [IsNoetherianRing Λ]
    [Module.Finite Λ k] :
    HasSmoothPresentation.{u, v, w} p ↔ IsFiniteDimensionalDeformationCategory.{u, v, w} p :=
  ⟨isFiniteDimensionalDeformationCategory_of_hasSmoothPresentation p,
    fun h => hasSmoothPresentation_of_hasMinimalPresentation p
      (hasMinimalPresentation_of_isFiniteDimensionalDeformationCategory p h)⟩

/-- When the residue field carries no nonzero `Λ`-derivation, a minimal smooth
prorepresentable presentation is normalized, so conditions (1) and (3) agree. The forward
implication is Tag 06KN; the converse is
`Deformation.GroupoidInFunctors.isNormalized_of_isMinimal_of_derivation_eq_zero`. -/
theorem hasNormalizedPresentation_iff_hasMinimalPresentation [IsNoetherianRing Λ]
    [Module.Finite Λ k] (hzero : ∀ δ : Derivation Λ k k, δ = 0) :
    HasNormalizedPresentation.{u, v, w} p ↔ HasMinimalPresentation.{u, v, w} p := by
  refine ⟨hasMinimalPresentation_of_hasNormalizedPresentation p, fun h => ?_⟩
  obtain ⟨G, hmin, hsmooth, hpro, hpres⟩ := h
  exact ⟨G, GroupoidInFunctors.isNormalized_of_isMinimal_of_derivation_eq_zero.{u, v, w}
    G hpro hsmooth hmin hzero, hsmooth, hpro, hpres⟩

/-- **Stacks Project, Tag 06TE**, the separable case. When `k` is separable over the image
field of `Λ` the residue field carries no nonzero `Λ`-derivation, so a minimal smooth
prorepresentable presentation is normalized and conditions (1) and (3) agree. -/
@[stacks 06TE "the separability clause of the tag: when k' ⊂ k is separable, condition (1), a \
normalized smooth prorepresentable presentation, is equivalent to the other three. Proved \
outright. Separability is read as Algebra.IsSeparable (residueImageField Λ k) k, and the \
equivalence of (1) with conditions (2), (3), (4) is this equivalence with (3) together with \
the equivalence of (2), (3), (4) in Deformation.hasSmoothPresentation_tfae; the four-way \
equivalence is assembled as Deformation.tfae_of_isSeparable"]
theorem hasNormalizedPresentation_iff_hasMinimalPresentation_of_isSeparable
    [IsNoetherianRing Λ] [Module.Finite Λ k]
    [Algebra.IsSeparable (residueImageField Λ k) k] :
    HasNormalizedPresentation.{u, v, w} p ↔ HasMinimalPresentation.{u, v, w} p :=
  hasNormalizedPresentation_iff_hasMinimalPresentation p
    derivation_eq_zero_of_residueImageField_separable

/-- **Stacks Project, Tag 06TE.** Conditions (2), (3) and (4) are equivalent, and (1) implies
them; when the residue field carries no nonzero `Λ`-derivation all four are equivalent.

The implications are (1) implies (3) and (3) implies (2), from Tag 06KN and the definitions,
(4) implies (3), from Tag 06L2, and (2) implies (4), from Tag 06L8; the equivalence of (1)
and (3) under `hzero` is the other half of Tag 06KN. -/
@[stacks 06TE "the tag: for ℱ cofibered in groupoids over 𝒞_Λ, conditions (2) a smooth \
prorepresentable presentation, (3) a minimal one, and (4) ℱ a deformation category with \
dim_k Tℱ and dim_k Inf(ℱ) finite, are equivalent and implied by (1) a normalized one, and all \
four are equivalent when k' ⊂ k is separable. Delivered outright and with no carried \
hypothesis: (1) ⟹ (3), (3) ⟹ (2), (4) ⟹ (3), (2) ⟹ (4) — the last from \
Deformation.hasSmoothPresentation_iff_isFiniteDimensionalDeformationCategory, Stacks 06L8 — \
and (3) ⟺ (1) whenever Der_Λ(k, k) vanishes. Nothing is assumed: this theorem takes no \
hypothesis beyond the chapter's standing IsNoetherianRing Λ and Module.Finite Λ k, and the \
vanishing of Der_Λ(k, k) is the antecedent of the fourth conjunct, which is proved outright \
as an implication. Separability of k' ⊂ k supplies that vanishing, by \
Deformation.derivation_eq_zero_of_residueImageField_separable, so the fourth conjunct is at \
least as strong as the source's separable clause; that clause itself, as the four-way \
equivalence, is Deformation.tfae_of_isSeparable, also carrying this tag. The final \
uniqueness clause of the tag is not here: it is Stacks 06L3, carried by this tag's \
add_to_stacks on Deformation.GroupoidInFunctors.nonempty_iso_of_presentations, and it too is \
delivered outright — the realisation of a 1-morphism of quotients by a morphism of groupoids \
in functors, which that proof attributes to Definition 06KB, is proved as \
Deformation.GroupoidInFunctors.exists_hom_of_morphismOver. No part of this tag is \
conditional. The statement is \
specialised to a hom-set \
universe of ℱ equal to the value universe v of the groupoids in functors, which is where \
Stacks 06L2 and Stacks 06L3 meet"]
theorem hasSmoothPresentation_tfae [IsNoetherianRing Λ] [Module.Finite Λ k] :
    (HasNormalizedPresentation.{u, v, w} p → HasMinimalPresentation.{u, v, w} p) ∧
      (HasSmoothPresentation.{u, v, w} p ↔ HasMinimalPresentation.{u, v, w} p) ∧
      (HasSmoothPresentation.{u, v, w} p ↔
        IsFiniteDimensionalDeformationCategory.{u, v, w} p) ∧
      ((∀ δ : Derivation Λ k k, δ = 0) →
        (HasNormalizedPresentation.{u, v, w} p ↔ HasMinimalPresentation.{u, v, w} p)) :=
  ⟨hasMinimalPresentation_of_hasNormalizedPresentation p,
    ⟨fun h => hasMinimalPresentation_of_isFiniteDimensionalDeformationCategory p
      (isFiniteDimensionalDeformationCategory_of_hasSmoothPresentation p h),
      hasSmoothPresentation_of_hasMinimalPresentation p⟩,
    hasSmoothPresentation_iff_isFiniteDimensionalDeformationCategory p,
    hasNormalizedPresentation_iff_hasMinimalPresentation p⟩

/-- **Stacks Project, Tag 06TE**, the four-way equivalence under separability. When `k` is
separable over the image field of `Λ`, a category cofibered in groupoids over `𝒞_Λ` admits a
presentation by a normalized smooth prorepresentable groupoid in functors if and only if it
admits one by a smooth prorepresentable groupoid in functors, if and only if it admits one by
a minimal smooth prorepresentable groupoid in functors, if and only if it is a deformation
category whose tangent space and whose space of infinitesimal automorphisms are
finite dimensional over `k`.

The cycle is (1) implies (3) by Tag 06KN, (3) implies (2) by the definitions, (2) implies (4)
by Tag 06L8, and (4) implies (1) by Tag 06L2 followed by the separable half of Tag 06KN. -/
@[stacks 06TE "the tag's final equivalence, assembled: under separability of k' ⊂ k the four \
conditions (1) a normalized smooth prorepresentable presentation, (2) a smooth \
prorepresentable one, (3) a minimal one, and (4) ℱ a deformation category with dim_k Tℱ and \
dim_k Inf(ℱ) finite are all equivalent. Proved outright, with no carried hypothesis. \
Separability is read as Algebra.IsSeparable (residueImageField Λ k) k. The statement is \
specialised to a hom-set universe of ℱ equal to the value universe v of the groupoids \
in functors, which is where Stacks 06L2 and Stacks 06L3 meet. The uniqueness clause of the \
tag \
is separate and is also delivered outright: see this tag's add_to_stacks \
on Deformation.GroupoidInFunctors.nonempty_iso_of_presentations"]
theorem tfae_of_isSeparable [IsNoetherianRing Λ] [Module.Finite Λ k]
    [Algebra.IsSeparable (residueImageField Λ k) k] :
    List.TFAE [HasNormalizedPresentation.{u, v, w} p, HasSmoothPresentation.{u, v, w} p,
      HasMinimalPresentation.{u, v, w} p,
      IsFiniteDimensionalDeformationCategory.{u, v, w} p] := by
  tfae_have 1 → 3 := hasMinimalPresentation_of_hasNormalizedPresentation p
  tfae_have 3 → 2 := hasSmoothPresentation_of_hasMinimalPresentation p
  tfae_have 2 → 4 := isFiniteDimensionalDeformationCategory_of_hasSmoothPresentation p
  tfae_have 4 → 1 := fun h =>
    (hasNormalizedPresentation_iff_hasMinimalPresentation_of_isSeparable p).2
      (hasMinimalPresentation_of_isFiniteDimensionalDeformationCategory p h)
  tfae_finish

end

end Deformation

add_to_stacks 06TE "the final uniqueness clause of the tag: the minimal smooth \
prorepresentable groupoids in functors which present a given category cofibered in groupoids \
over 𝒞_Λ are unique up to isomorphism. This is Stacks 06L3, delivered outright: the \
realisation it rests on — that a 1-morphism of quotients over 𝒞_Λ is, up to isomorphism of \
functors, the one induced by a morphism of groupoids in functors, the step the source proof \
attributes to Definition 06KB — is proved as \
Deformation.GroupoidInFunctors.exists_hom_of_morphismOver, for a prorepresentable source and \
a smooth target, which both presentations here supply. No part of Stacks 06TE is conditional; \
for the equivalence of the four conditions see \
Deformation.hasSmoothPresentation_tfae and Deformation.tfae_of_isSeparable"
  Deformation.GroupoidInFunctors.nonempty_iso_of_presentations
