module

public import StacksFrontier.Deformation.Applications.TwoFibreProductSixTermSequence
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.MapSquareZero
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.TangentTensorSplit

/-!
# Transferring surjectivity of infinitesimal automorphisms (Stacks 06JY)

Let `q : 𝒢 → ℱ` be a morphism of deformation categories over `𝒞_Λ` and let `z₀` be an object
of `𝒢` over the residue field. Tag 0DYN assumes that `Inf(𝒢) → Inf(ℱ)` is surjective and uses
Tag 06JY to deduce that `Inf(x'/x) → Inf(q(x')/q(x))` is surjective for every lifting arrow
`x' ⟶ x` over a small extension. This file carries out that deduction.

`Inf(𝒢) → Inf(ℱ)` is the induced linear map of Tag 07W6 on the tangent spaces of the
automorphism functors at the identity, `Deformation.inducedInfinitesimalLinearMapOfEq`. The
first step is to read its surjectivity as surjectivity on the automorphisms of the
dual-number pushforward of `z₀`: Tag 07W6 pins the induced map to conjugation by a comparison
arrow of dual-number pushforwards, and that comparison arrow is vertical, hence invertible.
Over the special fibre of a deformation category every automorphism of a pushforward is
infinitesimal, so no condition is left over.

The second step is the reduction of a small extension to the special fibre. The infinitesimal
automorphisms of `x'` over `x` are the automorphisms of an (RS) fibre square of `x'` with
itself over `x` that are trivial on the first projection; the difference coordinate
`(a₁, a₂) ↦ (ā₁, a₂ - a₁)` presents that square as a fibre square of `x'` with a pushforward
of `x'` along the split inclusion `A' ⟶ k ⊕ I`, so they are the automorphisms of that
pushforward, and the coordinate module `I` is then decomposed into lines.

## Main definitions

* `Deformation.chosenPushforwardsAt`: a choice of pushforwards of an object along every arrow
  out of its base.
* `Deformation.squareZeroUnderBaseCompare`, `Deformation.squareZeroUnderBaseIso`: the
  comparison of the square-zero extensions by one coordinate module under two bases.

## Main results

* `Deformation.surjective_mapFiberAut_dualNumbersUnder`: **the dual-number bridge.**
  Surjectivity of the induced linear map of Tag 07W6 is surjectivity on the automorphisms of
  the dual-number pushforward.
* `Deformation.squareZeroUnder_hom_comp_baseIso`: the comparison is compatible with the two
  structural arrows.
* `Deformation.surjective_mapRelativeInfinitesimalAutomorphisms_of_surjective_dualNumbers`:
  **the transfer of Tag 06JY.** Surjectivity on the automorphisms of the dual-number
  pushforward of a point gives surjectivity on the infinitesimal automorphisms along every
  arrow over a surjection whose kernel is annihilated by the maximal ideal.

## Implementation notes

The two base objects `Deformation.dualNumbersUnder` of `𝒢` at `z₀` and of `ℱ` at `q(z₀)` are
*propositionally* equal objects of `𝒞_Λ`, not equal ones: they are built from the two bases
`𝒢.p(z₀)` and `ℱ.p(q(z₀))`, which a morphism over `𝒞_Λ` identifies only up to its structural
equality. The comparison arrow of Tag 07W6 has one end in each of the two fibres, so its
existence already forces the two base objects to be equal, and
`Deformation.isHomLift_id_of_base_eq` is what moves verticality across that equality. No
transport of the automorphism groups themselves is needed: the conjugate of an automorphism by
the comparison arrow is written out as a composite of three arrows.

## References

* [Stacks Project, Tag 06JY](https://stacks.math.columbia.edu/tag/06JY)
* [Stacks Project, Tag 07W6](https://stacks.math.columbia.edu/tag/07W6)
-/

@[expose] public section

namespace Deformation

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u v w uG vG uF vF

/-! ### Surjectivity on the automorphisms of the dual-number pushforward -/

section Conj

variable {C : Type*} [Category C] {X : Type*} [Category X] {p : X ⥤ C}

/-- The conjugate of an automorphism of an object of a fibre by an invertible arrow lying over
an identity, read as an automorphism of the source of that arrow. -/
public noncomputable def conjFiberAut {R S : C} {x : p.Fiber R} {y : p.Fiber S} (H : x.1 ⟶ y.1)
    [IsIso H] (hH : p.IsHomLift (𝟙 R) H) (b : Aut y) : Aut x :=
  have hbase : R = S := (IsHomLift.codomain_eq p (𝟙 R) H).symm.trans y.2
  have := hH
  have := isHomLift_id_of_base_eq hbase.symm b.asIso.hom.val b.asIso.hom.2
  have := isHomLift_id_of_base_eq hbase.symm b.asIso.inv.val b.asIso.inv.2
  have : p.IsHomLift (𝟙 R) (inv H) := by simpa using IsHomLift.inv p (𝟙 R) H
  have hhi : b.asIso.hom.val ≫ b.asIso.inv.val = 𝟙 _ := congrArg Subtype.val b.asIso.hom_inv_id
  have hih : b.asIso.inv.val ≫ b.asIso.hom.val = 𝟙 _ := congrArg Subtype.val b.asIso.inv_hom_id
  Aut.of
  { hom := ⟨H ≫ b.asIso.hom.val ≫ inv H,
      IsHomLift.comp_of_lift_id p _ H (b.asIso.hom.val ≫ inv H)⟩
    inv := ⟨H ≫ b.asIso.inv.val ≫ inv H,
      IsHomLift.comp_of_lift_id p _ H (b.asIso.inv.val ≫ inv H)⟩
    hom_inv_id := by
      apply Functor.Fiber.hom_ext
      change (H ≫ b.asIso.hom.val ≫ inv H) ≫ H ≫ b.asIso.inv.val ≫ inv H = 𝟙 _
      simp only [Category.assoc, IsIso.inv_hom_id_assoc]
      rw [← Category.assoc b.asIso.hom.val, hhi, Category.id_comp, IsIso.hom_inv_id]
    inv_hom_id := by
      apply Functor.Fiber.hom_ext
      change (H ≫ b.asIso.inv.val ≫ inv H) ≫ H ≫ b.asIso.hom.val ≫ inv H = 𝟙 _
      simp only [Category.assoc, IsIso.inv_hom_id_assoc]
      rw [← Category.assoc b.asIso.inv.val, hih, Category.id_comp, IsIso.hom_inv_id] }

/-- The underlying arrow of the conjugate automorphism is the conjugate arrow. -/
public theorem conjFiberAut_hom_val {R S : C} {x : p.Fiber R} {y : p.Fiber S} (H : x.1 ⟶ y.1)
    [IsIso H] (hH : p.IsHomLift (𝟙 R) H) (b : Aut y) :
    (conjFiberAut H hH b).asIso.hom.val = H ≫ b.asIso.hom.val ≫ inv H :=
  rfl

end Conj

section DualNumbers

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {𝓖 : BasedCategory.{vG, uG} (ArtinianLocalAlgCat.{u, max v w, w} Λ k)}
  {𝓕 : BasedCategory.{vF, uF} (ArtinianLocalAlgCat.{u, max v w, w} Λ k)}

/-- **The dual-number bridge.** If the induced linear map of Tag 07W6 on infinitesimal
automorphisms is surjective, then the morphism is surjective on the automorphisms of the
dual-number pushforward of `z₀`.

Tag 07W6 provides a vertical comparison arrow `H` of the two dual-number pushforwards which
conjugates an infinitesimal automorphism into its image; since `H` is vertical it is
invertible, and over a thin special fibre every automorphism of a dual-number pushforward is
infinitesimal, so conjugation by `H` identifies the two automorphism groups with the two
groups of infinitesimal automorphisms. -/
public theorem surjective_mapFiberAut_dualNumbersUnder (q : BasedFunctor 𝓖 𝓕)
    (hrsG : SatisfiesRS 𝓖.p) (hrsF : SatisfiesRS 𝓕.p)
    (hthinF : Quiver.IsThin (𝓕.p.Fiber (residueFieldObject.{u, v, w} Λ k)))
    {z₀ : 𝓖.obj} (PG : ChosenPushforwardsAt 𝓖.p z₀)
    (PF : ChosenPushforwardsAt 𝓕.p (q.obj z₀))
    (hsurj :
      letI := naturalLocalizedTangentAddCommGroup PG hrsG
      letI := naturalLocalizedTangentModule PG hrsG
      letI := naturalLocalizedTangentAddCommGroup PF hrsF
      letI := naturalLocalizedTangentModule PF hrsF
      Function.Surjective
        (inducedInfinitesimalLinearMapOfEq q.toFunctor q.w hrsG hrsF PG PF)) :
    Function.Surjective (mapFiberAut q (PG.obj (dualNumbersUnder (p := 𝓖.p) (x := z₀)))) := by
  let := naturalLocalizedTangentAddCommGroup PG hrsG
  let := naturalLocalizedTangentModule PG hrsG
  let := naturalLocalizedTangentAddCommGroup PF hrsF
  let := naturalLocalizedTangentModule PF hrsF
  have hcofF := hrsF.1
  obtain ⟨H, hH, -, hconj⟩ :=
    inducedInfinitesimalLinearMapOfEq_spec q.toFunctor q.w hrsG hrsF PG PF
  -- `H` is vertical, hence invertible
  have hIso : IsIso H := isIso_of_isHomLift_id hcofF H hH
  -- over a thin special fibre every automorphism of the dual-number pushforward is
  -- infinitesimal
  have htop := ker_transportAutHom_eq_top_of_isThin.{u, v, w, uF, vF} hcofF PF hthinF
    (tangentReduction (p := 𝓕.p) (x := q.obj z₀))
  intro b
  let β := conjFiberAut H hH b
  have hβmem : β ∈ MonoidHom.ker
      (PF.transportAutHom (tangentReduction (p := 𝓕.p) (x := q.obj z₀))) := by
    rw [htop]
    exact Subgroup.mem_top β
  -- pull `β` back along the two identifications
  obtain ⟨tG, htG⟩ := hsurj ((localizedTangentEquivKernel PF).symm ⟨β, hβmem⟩)
  refine ⟨(localizedTangentEquivKernel PG tG).1, ?_⟩
  have hval : (localizedTangentEquivKernel PF
      (inducedInfinitesimalLinearMapOfEq q.toFunctor q.w hrsG hrsF PG PF tG)).1 = β := by
    rw [htG]
    exact congrArg Subtype.val ((localizedTangentEquivKernel PF).apply_symm_apply ⟨β, hβmem⟩)
  have hkey := hconj tG
  rw [show (localizedTangentEquivKernel PF
      (inducedInfinitesimalLinearMapOfEq q.toFunctor q.w hrsG hrsF PG PF tG)).1.asIso.hom.val =
      H ≫ b.asIso.hom.val ≫ inv H from congrArg
      (fun c : Aut (PF.obj (dualNumbersUnder (p := 𝓕.p) (x := q.obj z₀))) => c.asIso.hom.val)
      hval] at hkey
  have hcancel : H ≫ b.asIso.hom.val =
      H ≫ q.map (localizedTangentEquivKernel PG tG).1.asIso.hom.val := by
    refine Eq.trans ?_ hkey
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  exact Aut.ext (Iso.ext (Functor.Fiber.hom_ext ((cancel_epi H).mp hcancel).symm))

end DualNumbers

/-! ### A choice of pushforwards -/

section Chosen

universe u₁ v₁

variable {F : Type u₁} [Category.{v₁} F] {C : Type u} [Category.{v} C] {p : F ⥤ C}

/-- **A choice of pushforwards exists.** The chosen-pushforward data of Tag 06JT at an object
of a category cofibered in groupoids is bookkeeping, not a hypothesis. -/
public noncomputable def chosenPushforwardsAt (hp : IsCofiberedInGroupoids p) (x : F) :
    ChosenPushforwardsAt p x :=
  ChosenPushforwardsAt.ofCofiberedInGroupoids hp
    (fun U => ⟨(exists_pushforward hp U.hom x rfl).choose,
      letI := (exists_pushforward hp U.hom x rfl).choose_spec.choose_spec
      IsHomLift.codomain_eq p U.hom
        (exists_pushforward hp U.hom x rfl).choose_spec.choose⟩)
    (fun U => (exists_pushforward hp U.hom x rfl).choose_spec.choose)
    (fun U => (exists_pushforward hp U.hom x rfl).choose_spec.choose_spec)

end Chosen

/-! ### The square-zero extension under two bases joined by an arrow -/

section BaseCompare

universe u₁ v₁

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {F : Type u₁} [Category.{v₁} F] {p : F ⥤ ArtinianLocalAlgCat.{u, w, w} Λ k}

/-- The identity of `TrivSqZeroExt k M`, read as a morphism of `𝒞_Λ` between the square-zero
extensions by `M` under the bases of two objects. The two objects of `𝒞_Λ` have the same
carrier, the same ring and the same reduction; only the structural `Λ`-algebra maps differ,
and they are propositionally equal. -/
public noncomputable def squareZeroUnderBaseCompare (x y : F) (M : FGModuleCat.{w} k) :
    (squareZeroUnder.{u, w, w} p x M).right ⟶ (squareZeroUnder.{u, w, w} p y M).right where
  hom :=
    { toFun := fun z => z
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun t => by
        change TrivSqZeroExt.inl ((p.obj x).residueEquiv
            (residue (p.obj x) (algebraMap Λ (p.obj x) t))) =
          TrivSqZeroExt.inl ((p.obj y).residueEquiv
            (residue (p.obj y) (algebraMap Λ (p.obj y) t)))
        rw [residueEquiv_residue_algebraMap (p.obj x) t,
          residueEquiv_residue_algebraMap (p.obj y) t] }
  isLocal := ⟨fun _ ha => ha⟩
  residue_comm := fun _ => rfl

/-- **The square-zero extensions by `M` under two bases are isomorphic.** -/
public noncomputable def squareZeroUnderBaseIso (x y : F) (M : FGModuleCat.{w} k) :
    (squareZeroUnder.{u, w, w} p x M).right ≅ (squareZeroUnder.{u, w, w} p y M).right :=
  isoOfBijectiveHom (squareZeroUnderBaseCompare.{u, w} (p := p) x y M)
    ⟨fun _ _ h => h, fun z => ⟨z, rfl⟩⟩

/-- **The comparison is compatible with the two structural arrows.** An arrow between the two
bases carries the structural arrow of the square-zero extension under the one to the
structural arrow under the other. -/
public theorem squareZeroUnder_hom_comp_baseIso {x y : F} (ρ : p.obj x ⟶ p.obj y)
    (M : FGModuleCat.{w} k) :
    (squareZeroUnder.{u, w, w} p x M).hom ≫
        (squareZeroUnderBaseIso.{u, w} (p := p) x y M).hom =
      ρ ≫ (squareZeroUnder.{u, w, w} p y M).hom := by
  refine ArtinianLocalAlgCat.hom_ext (AlgHom.ext fun a => ?_)
  show TrivSqZeroExt.inl ((p.obj x).residueEquiv (residue (p.obj x) a)) =
    TrivSqZeroExt.inl ((p.obj y).residueEquiv (residue (p.obj y) (ρ.hom a)))
  rw [ρ.residue_comm a]

end BaseCompare

/-! ### The reduction of a small extension to the split square-zero extension -/

section Reduction

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {𝓖 : BasedCategory.{vG, uG} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
  {𝓕 : BasedCategory.{vF, uF} (ArtinianLocalAlgCat.{u, w, w} Λ k)}

/-- **(RS) detects fibre squares.** A commutative square of `𝒢` lying over a fibre square of
`𝒞_Λ` whose second leg is surjective is a fibre square. -/
public theorem isPullback_of_isHomLift_of_satisfiesRS (hrsG : SatisfiesRS 𝓖.p)
    {D A₁ A₂ A : ArtinianLocalAlgCat.{u, w, w} Λ k} {π₁ : D ⟶ A₁} {π₂ : D ⟶ A₂}
    {g₁ : A₁ ⟶ A} {g₂ : A₂ ⟶ A}
    {z : 𝓖.p.Fiber D} {x₁ : 𝓖.p.Fiber A₁} {x₂ : 𝓖.p.Fiber A₂} {x : 𝓖.p.Fiber A}
    {c₁ : z.1 ⟶ x₁.1} {c₂ : z.1 ⟶ x₂.1} {f₁ : x₁.1 ⟶ x.1} {f₂ : x₂.1 ⟶ x.1}
    (hc₁ : 𝓖.p.IsHomLift π₁ c₁) (hc₂ : 𝓖.p.IsHomLift π₂ c₂)
    (hf₁ : 𝓖.p.IsHomLift g₁ f₁) (hf₂ : 𝓖.p.IsHomLift g₂ f₂)
    (hcomm : c₁ ≫ f₁ = c₂ ≫ f₂) (hbase : IsPullback π₁ π₂ g₁ g₂)
    (hg₂ : Function.Surjective g₂.hom) :
    IsPullback c₁ c₂ f₁ f₂ := by
  obtain ⟨z, rfl⟩ := z
  obtain ⟨x₁, rfl⟩ := x₁
  obtain ⟨x₂, rfl⟩ := x₂
  obtain ⟨x, rfl⟩ := x
  obtain rfl := IsHomLift.eq_of_isHomLift 𝓖.p π₁ c₁
  obtain rfl := IsHomLift.eq_of_isHomLift 𝓖.p π₂ c₂
  obtain rfl := IsHomLift.eq_of_isHomLift 𝓖.p g₁ f₁
  obtain rfl := IsHomLift.eq_of_isHomLift 𝓖.p g₂ f₂
  obtain ⟨hlim⟩ := isLimit_of_map_isLimit hrsG f₁ f₂ (PullbackCone.mk c₁ c₂ hcomm) hg₂
    ⟨IsLimit.ofIsoLimit hbase.isLimit
      (PullbackCone.ext (Iso.refl _) (Category.id_comp _).symm (Category.id_comp _).symm)⟩
  exact IsPullback.of_isLimit hlim

/-- **Lines at a point joined to `z₀`.** If `q` is surjective on the automorphisms of the
dual-number pushforward of `z₀`, then it is surjective on the automorphisms of the chosen
pushforward of any `Z` with an arrow to `z₀` along the square-zero extension by a line. -/
public theorem surjective_mapFiberAut_squareZeroUnder_ulift_of_arrow (q : BasedFunctor 𝓖 𝓕)
    (hG : IsCofiberedInGroupoids 𝓖.p) (hF : IsCofiberedInGroupoids 𝓕.p)
    {Z z₀ : 𝓖.obj} (PG : ChosenPushforwardsAt 𝓖.p z₀) (ψ₀ : Z ⟶ z₀)
    (hline : Function.Surjective
      (mapFiberAut q (PG.obj (dualNumbersUnder (p := 𝓖.p) (x := z₀))))) :
    Function.Surjective (mapFiberAut q
      (chosenPushforwardsAt hG Z |>.obj
        (squareZeroUnder.{u, w, w} 𝓖.p Z (FGModuleCat.of k (ULift.{w} k))))) := by
  have hwψ : (squareZeroUnder.{u, w, w} 𝓖.p Z (FGModuleCat.of k (ULift.{w} k))).hom =
      (𝓖.p.map ψ₀ ≫
          (squareZeroUnder.{u, w, w} 𝓖.p z₀ (FGModuleCat.of k (ULift.{w} k))).hom) ≫
        (squareZeroUnderBaseIso.{u, w} (p := 𝓖.p) Z z₀
          (FGModuleCat.of k (ULift.{w} k))).symm.hom := by
    exact (Iso.eq_comp_inv _).2 (squareZeroUnder_hom_comp_baseIso.{u, w} (p := 𝓖.p)
      (𝓖.p.map ψ₀) (FGModuleCat.of k (ULift.{w} k)))
  refine surjective_mapFiberAut_of_pushforward q hG hF
    (𝓖.p.map ψ₀ ≫ (squareZeroUnder.{u, w, w} 𝓖.p z₀ (FGModuleCat.of k (ULift.{w} k))).hom)
    (squareZeroUnderBaseIso.{u, w} (p := 𝓖.p) Z z₀ (FGModuleCat.of k (ULift.{w} k))).symm
    (ψ₀ ≫ PG.inclusion (dualNumbersUnder (p := 𝓖.p) (x := z₀)))
    (isHomLift_comp (IsHomLift.map 𝓖.p ψ₀)
      (PG.inclusion_cocartesian (dualNumbersUnder (p := 𝓖.p) (x := z₀))).1)
    ((chosenPushforwardsAt hG Z).inclusion
      (squareZeroUnder.{u, w, w} 𝓖.p Z (FGModuleCat.of k (ULift.{w} k))))
    (hwψ ▸ ((chosenPushforwardsAt hG Z).inclusion_cocartesian
      (squareZeroUnder.{u, w, w} 𝓖.p Z (FGModuleCat.of k (ULift.{w} k)))).1) hline

/-- **Pushforwards along the split inclusion.** If `q` is surjective on the automorphisms of
the dual-number pushforward of a point `z₀` joined to `Z`, then it is surjective on the
automorphisms of every pushforward of `Z` along the split inclusion `A' ⟶ k ⊕ I`. -/
public theorem surjective_mapFiberAut_of_isHomLift_kernelSplitInclusion (q : BasedFunctor 𝓖 𝓕)
    (hrsG : SatisfiesRS 𝓖.p) (hrsF : SatisfiesRS 𝓕.p)
    (hthinG : Quiver.IsThin (𝓖.p.Fiber (residueFieldObject.{u, w, w} Λ k)))
    (hthinF : Quiver.IsThin (𝓕.p.Fiber (residueFieldObject.{u, w, w} Λ k)))
    {Z z₀ : 𝓖.obj} (PG : ChosenPushforwardsAt 𝓖.p z₀) (ψ₀ : Z ⟶ z₀)
    (hline : Function.Surjective
      (mapFiberAut q (PG.obj (dualNumbersUnder (p := 𝓖.p) (x := z₀)))))
    {A : ArtinianLocalAlgCat.{u, w, w} Λ k} (f : 𝓖.p.obj Z ⟶ A) (hf : Function.Surjective f.hom)
    (hann : ∀ a : 𝓖.p.obj Z, a ∈ maximalIdeal (𝓖.p.obj Z) →
      ∀ i : RingHom.ker f.hom.toRingHom, a * (i : 𝓖.p.obj Z) = 0)
    {y : 𝓖.p.Fiber (infinitesimalDifferenceMap f hf hann).target} (i : Z ⟶ y.1)
    (hi : 𝓖.p.IsHomLift (kernelSplitInclusion f hf hann) i) :
    Function.Surjective (mapFiberAut q y) := by
  have hsplit : (squareZeroUnder.{u, w, w} 𝓖.p Z (kernelCoordinateModule f hann)).hom ≫
      (kernelTrivialExtensionIso.{u, w, uG, vG} (p := 𝓖.p) (x := Z) f hf hann).symm.hom =
      kernelSplitInclusion f hf hann := by
    exact (Iso.comp_inv_eq _).2 (kernelSplitInclusion_comp_kernelTrivialExtensionIso.{u, w, uG, vG}
      (p := 𝓖.p) (x := Z) f hf hann).symm
  refine surjective_mapFiberAut_of_pushforward q hrsG.1 hrsF.1
    (squareZeroUnder.{u, w, w} 𝓖.p Z (kernelCoordinateModule f hann)).hom
    (kernelTrivialExtensionIso.{u, w, uG, vG} (p := 𝓖.p) (x := Z) f hf hann).symm
    ((chosenPushforwardsAt hrsG.1 Z).inclusion
      (squareZeroUnder.{u, w, w} 𝓖.p Z (kernelCoordinateModule f hann)))
    ((chosenPushforwardsAt hrsG.1 Z).inclusion_cocartesian
      (squareZeroUnder.{u, w, w} 𝓖.p Z (kernelCoordinateModule f hann))).1 i (hsplit ▸ hi)
    (surjective_mapFiberAut_squareZeroUnder q hrsG hrsF hthinG hthinF
      (chosenPushforwardsAt hrsG.1 Z)
      (surjective_mapFiberAut_squareZeroUnder_ulift_of_arrow q hrsG.1 hrsF.1 PG ψ₀ hline)
      (kernelCoordinateModule f hann))

/-- **The transfer of Tag 06JY.** Let `q : 𝒢 → ℱ` be a morphism of categories cofibered in
groupoids over `𝒞_Λ` satisfying (RS) whose special fibres are thin, let `r : z ⟶ t` be a
lifting arrow over a surjection whose kernel is annihilated by the maximal ideal, and let
`ψ₀ : z ⟶ z₀` be an arrow to a point `z₀` carrying chosen pushforwards. If `q` is surjective
on the automorphisms of the dual-number pushforward of `z₀`, then it is surjective on the
infinitesimal automorphisms of `z` relative to `t`.

This is the deduction Tag 0DYN makes from Tag 06JY. The infinitesimal automorphisms of `z`
over `t` are the automorphisms of an (RS) fibre square of `z` with itself trivial on the
first projection, and that square is also a fibre square of `z` with a pushforward `z[I]` of
`z` along the split inclusion `A' ⟶ k ⊕ I` over the special fibre; so they are the
automorphisms of `z[I]`, where the coordinate module `I` is decomposed into lines. -/
public theorem surjective_mapRelativeInfinitesimalAutomorphisms_of_surjective_dualNumbers
    (q : BasedFunctor 𝓖 𝓕) (hrsG : SatisfiesRS 𝓖.p) (hrsF : SatisfiesRS 𝓕.p)
    (hthinG : Quiver.IsThin (𝓖.p.Fiber (residueFieldObject.{u, w, w} Λ k)))
    (hthinF : Quiver.IsThin (𝓕.p.Fiber (residueFieldObject.{u, w, w} Λ k)))
    {B A : ArtinianLocalAlgCat.{u, w, w} Λ k} (g : B ⟶ A) (hg : Function.Surjective g.hom)
    (hann : ∀ a : B, a ∈ maximalIdeal B → ∀ i : RingHom.ker g.hom.toRingHom, a * (i : B) = 0)
    {z : 𝓖.p.Fiber B} {t : 𝓖.p.Fiber A} (r : z.1 ⟶ t.1) (hr : 𝓖.p.IsHomLift g r)
    {z₀ : 𝓖.obj} (PG : ChosenPushforwardsAt 𝓖.p z₀) (ψ₀ : z.1 ⟶ z₀)
    (hline : Function.Surjective
      (mapFiberAut q (PG.obj (dualNumbersUnder (p := 𝓖.p) (x := z₀))))) :
    Function.Surjective (mapRelativeInfinitesimalAutomorphisms q hrsG.1 hrsF.1 g r hr) := by
  obtain ⟨Z, rfl⟩ := z
  obtain ⟨T, rfl⟩ := t
  have hrinst := hr
  obtain rfl : g = 𝓖.p.map r := IsHomLift.eq_of_isHomLift 𝓖.p g r
  -- the (RS) fibre square of `r` with itself
  obtain ⟨cone, ⟨hlim⟩, ⟨hlimp⟩⟩ := hrsG.2 r r hg
  have hsq : IsPullback cone.fst cone.snd r r := IsPullback.of_isLimit hlim
  have hbase0 : IsPullback (𝓖.p.map cone.fst) (𝓖.p.map cone.snd) (𝓖.p.map r) (𝓖.p.map r) :=
    IsPullback.of_isLimit hlimp
  -- a pushforward of `Z` to the special fibre
  obtain ⟨X₀, φ₀, hφ₀⟩ := exists_pushforward hrsG.1 (residueMorphism (𝓖.p.obj Z)) Z rfl
  have hφ₀inst := hφ₀
  let x₀ : 𝓖.p.Fiber (residueFieldObject.{u, w, w} Λ k) :=
    ⟨X₀, IsHomLift.codomain_eq 𝓖.p (residueMorphism (𝓖.p.obj Z)) φ₀⟩
  -- the diagonal of the base fibre square, and the difference coordinate
  let d : 𝓖.p.obj Z ⟶ 𝓖.p.obj cone.pt := hbase0.lift (𝟙 _) (𝟙 _) rfl
  have hd₁ : d ≫ 𝓖.p.map cone.fst = 𝟙 (𝓖.p.obj Z) := hbase0.lift_fst _ _ _
  have hd₂ : d ≫ 𝓖.p.map cone.snd = 𝟙 (𝓖.p.obj Z) := hbase0.lift_snd _ _ _
  obtain ⟨γ, hbase, hdγ⟩ := exists_isPullback_kernelTrivialExtension_diagonal (𝓖.p.map r) hg
    hann hbase0 d hd₁ hd₂
  obtain ⟨XI, cI, hcI⟩ := exists_pushforward hrsG.1 γ cone.pt rfl
  have hcIinst := hcI
  let xI : 𝓖.p.Fiber (infinitesimalDifferenceMap (𝓖.p.map r) hg hann).target :=
    ⟨XI, IsHomLift.codomain_eq 𝓖.p γ cI⟩
  have := IsHomLift.map 𝓖.p cone.fst
  have := isStronglyCocartesian_of_isCofiberedInGroupoids hrsG.1 γ cI hcI
  let fI : XI ⟶ X₀ := Functor.IsStronglyCocartesian.map 𝓖.p γ cI hbase.w (cone.fst ≫ φ₀)
  have hfac : cI ≫ fI = cone.fst ≫ φ₀ :=
    Functor.IsStronglyCocartesian.fac 𝓖.p γ cI hbase.w (cone.fst ≫ φ₀)
  have hfI : 𝓖.p.IsHomLift
      (residueMorphism (infinitesimalDifferenceMap (𝓖.p.map r) hg hann).target) fI :=
    inferInstance
  have hsqI : IsPullback cone.fst cI φ₀ fI :=
    isPullback_of_isHomLift_of_satisfiesRS hrsG (z := ⟨cone.pt, rfl⟩) (x₁ := ⟨Z, rfl⟩)
      (x₂ := xI) (x := x₀) (IsHomLift.map 𝓖.p cone.fst) hcI hφ₀ hfI hfac.symm hbase
      (surjective_hom_residueMorphism _)
  -- the images of the two fibre squares in `ℱ`
  have hsqB : IsPullback (q.map cone.fst) (q.map cone.snd) (q.map r) (q.map r) :=
    isPullback_map_of_satisfiesRS q hrsF (z := ⟨cone.pt, rfl⟩) (x₁ := ⟨Z, rfl⟩)
      (x₂ := ⟨Z, rfl⟩) (x := ⟨T, rfl⟩) (IsHomLift.map 𝓖.p cone.fst)
      (IsHomLift.map 𝓖.p cone.snd) (IsHomLift.map 𝓖.p r) (IsHomLift.map 𝓖.p r) hsq.w
      hbase0 hg
  have hsqIB : IsPullback (q.map cone.fst) (q.map cI) (q.map φ₀) (q.map fI) :=
    isPullback_map_of_satisfiesRS q hrsF (z := ⟨cone.pt, rfl⟩) (x₁ := ⟨Z, rfl⟩)
      (x₂ := xI) (x := x₀) (IsHomLift.map 𝓖.p cone.fst) hcI hφ₀ hfI hsqI.w hbase
      (surjective_hom_residueMorphism _)
  -- the two applications of the fibre-square identification
  refine (surjective_mapRelativeInfinitesimalAutomorphisms_fibreSquare_iff q hrsG.1 hrsF.1
    (z := ⟨cone.pt, rfl⟩) (x₁ := ⟨Z, rfl⟩) (x₂ := ⟨Z, rfl⟩) (x := ⟨T, rfl⟩)
    (IsHomLift.map 𝓖.p cone.fst) (IsHomLift.map 𝓖.p cone.snd) (IsHomLift.map 𝓖.p r)
    hsq hsqB hbase0).1 ?_
  refine (surjective_mapRelativeInfinitesimalAutomorphisms_fibreSquare_iff q hrsG.1 hrsF.1
    (z := ⟨cone.pt, rfl⟩) (x₁ := ⟨Z, rfl⟩) (x₂ := xI) (x := x₀)
    (IsHomLift.map 𝓖.p cone.fst) hcI hfI hsqI hsqIB hbase).2 ?_
  refine surjective_mapRelativeInfinitesimalAutomorphisms_of_surjective_mapFiberAut q hrsG.1
    hrsF.1 (x' := xI) (x := x₀)
    (residueMorphism (infinitesimalDifferenceMap (𝓖.p.map r) hg hann).target) fI hfI
    hthinG ?_
  -- the comparison arrow from `Z` to the fibre square, and on to `xI`
  let v : Z ⟶ cone.pt := hsq.lift (𝟙 Z) (𝟙 Z) rfl
  have hv₁ : v ≫ cone.fst = 𝟙 Z := hsq.lift_fst _ _ _
  have hv₂ : v ≫ cone.snd = 𝟙 Z := hsq.lift_snd _ _ _
  have hvd : 𝓖.p.map v = d := by
    refine hbase0.hom_ext ?_ ?_
    · rw [← 𝓖.p.map_comp, hv₁, 𝓖.p.map_id, hd₁]
    · rw [← 𝓖.p.map_comp, hv₂, 𝓖.p.map_id, hd₂]
  have hvhl : 𝓖.p.IsHomLift d v := hvd ▸ IsHomLift.map 𝓖.p v
  have hsplithl : 𝓖.p.IsHomLift (kernelSplitInclusion (𝓖.p.map r) hg hann) (v ≫ cI) := by
    rw [← hdγ]
    exact isHomLift_comp hvhl hcI
  exact surjective_mapFiberAut_of_isHomLift_kernelSplitInclusion q hrsG hrsF hthinG hthinF PG
    ψ₀ hline (𝓖.p.map r) hg hann (y := xI) (v ≫ cI) hsplithl

end Reduction

end Deformation

end
