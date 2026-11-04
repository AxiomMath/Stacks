module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.StructureSheafIsoNearSpecialFibreReduction
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.StructureSheafIsoNearSpecialFibreTransport
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.StructureSheafMono
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.MorphismDescent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Contractions over a local base

Let `Λ` be a local ring with closed point `s`, and `f : X ⟶ Y` a proper morphism of schemes over
`Spec Λ` with `Y` universally closed over `Spec Λ`, `X` flat along `X_s`, and the fibres of
`f_s` of dimension at most one. If `𝒪_{Y_s} ≅ f_{s,*}𝒪_{X_s}` and `R¹f_{s,*}𝒪_{X_s} = 0`, then
`𝒪_Y ≅ f_*𝒪_X` on all of `Y`: by Stacks 0E7L this holds on an open neighbourhood of `Y_s`, and
every point of `Y` specializes into `Y_s`, the image in `Spec Λ` of the closed complement being
closed and missing the closed point. In particular `f` is scheme-theoretically dominant.

This is the scheme-theoretic dominance of `c₁` that the reduction of Stacks 0E89 from a
Noetherian local ring to its completion uses: it makes two morphisms out of `Y₁` (and out of any
flat base change of it) agreeing after `c₁` equal, so an isomorphism `Y₁,T ≅ Y₂,T` compatible with
the `cᵢ` over a faithfully flat quasi-compact `T ⟶ S` (the completion) satisfies the descent
condition and descends (Stacks 040L, 02L4).

## Main results

* `AlgebraicGeometry.isIso_unitToPushforwardUnit_of_specialFibre_of_isLocalRing`: the statement
  above.
* `AlgebraicGeometry.isSchemeTheoreticallyDominant_of_specialFibre_of_isLocalRing`: `f` is
  scheme-theoretically dominant.
* `AlgebraicGeometry.eq_of_comp_eq_of_isSchemeTheoreticallyDominant`: two morphisms into a
  separated scheme agreeing after a scheme-theoretically dominant morphism are equal.
* `AlgebraicGeometry.exists_desc_of_isSchemeTheoreticallyDominant`,
  `AlgebraicGeometry.exists_iso_desc_of_isSchemeTheoreticallyDominant`: a morphism (an isomorphism)
  `Y₁,T ⟶ Y₂,T` over a surjective flat quasi-compact `T ⟶ S` compatible with `cᵢ : X ⟶ Yᵢ`, `c₁`
  scheme-theoretically dominant and `Y₂` separated, descends to one `Y₁ ⟶ Y₂` with `c₁ ≫ ψ = c₂`.

## References

* [Stacks Project, Tag 0E89](https://stacks.math.columbia.edu/tag/0E89)
* [Stacks Project, Tag 0E7L](https://stacks.math.columbia.edu/tag/0E7L)
* [Stacks Project, Tag 040L](https://stacks.math.columbia.edu/tag/040L)
* [Stacks Project, Tag 02L4](https://stacks.math.columbia.edu/tag/02L4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

namespace AlgebraicGeometry

variable {Λ : Type u} [CommRing Λ] [IsLocalRing Λ] {X Y : Scheme.{u}}

/-- **`𝒪_Y ≅ f_*𝒪_X` over a local base, from the special fibre.** Let `f : X ⟶ Y` be a proper
morphism over `Spec Λ`, `Λ` local with closed point `s`, with `Y` universally closed over
`Spec Λ`, both locally of finite presentation over `Spec Λ`, `X` flat along `X_s`, and the fibres
of `f_s : X_s ⟶ Y_s` of dimension at most one. If `R¹f_{s,*}𝒪_{X_s} = 0` and
`𝒪_{Y_s} ≅ f_{s,*}𝒪_{X_s}`, then `𝒪_Y ≅ f_*𝒪_X`. Stacks 0E7L gives the isomorphism on stalks
near every point of `Y_s`, and every point of `Y` specializes into `Y_s`. -/
theorem isIso_unitToPushforwardUnit_of_specialFibre_of_isLocalRing (f : X ⟶ Y)
    (q : Y ⟶ Spec (.of Λ)) [LocallyOfFinitePresentation (f ≫ q)] [LocallyOfFinitePresentation q]
    [IsProper f] [UniversallyClosed q]
    (hflat : ∀ x : X, (f ≫ q) x = IsLocalRing.closedPoint Λ →
      IsFlatAt (f ≫ q).toLRSHom.toShHom x)
    (hdim : ∀ y : q.fiber (IsLocalRing.closedPoint Λ),
      topologicalKrullDim ((Stacks.Flatness.fiberHom f q (IsLocalRing.closedPoint Λ)).fiber y) ≤
        ((1 : ℕ) : WithBot ℕ∞))
    (hR : IsZero (firstDirectImageStructureSheaf
      (pullback.snd f (q.fiberι (IsLocalRing.closedPoint Λ)))))
    (hiso : IsIso (Scheme.Modules.unitToPushforwardUnit
      (pullback.snd f (q.fiberι (IsLocalRing.closedPoint Λ))))) :
    IsIso (Scheme.Modules.unitToPushforwardUnit f) := by
  choose W hyW hW using fun y : {y : Y // q y = IsLocalRing.closedPoint Λ} =>
    exists_isOpen_bijective_stalk_of_mem_fiber f q _ hflat hdim hR hiso y.1 y.2
  refine isIso_of_bijective_modulesStalkFunctor_map _ fun y => ?_
  obtain ⟨y', hy'⟩ : ∃ y' : {y : Y // q y = IsLocalRing.closedPoint Λ}, y ∈ W y' := by
    by_contra hne
    push Not at hne
    let C : Set Y := (⋃ y', (W y' : Set Y))ᶜ
    have hC : IsClosed C := (isOpen_iUnion fun y' => (W y').isOpen).isClosed_compl
    have hyC : y ∈ C := by
      simp only [C, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
      exact hne
    obtain ⟨y', hy'C, hy'⟩ :=
      (IsLocalRing.specializes_closedPoint (q y)).mem_closed (q.isClosedMap _ hC) ⟨y, hyC, rfl⟩
    simp only [C, Set.mem_compl_iff, Set.mem_iUnion, not_exists] at hy'C
    exact hy'C ⟨y', hy'⟩ (hyW ⟨y', hy'⟩)
  exact hW y' y hy'

/-- **A morphism with `𝒪_Y ≅ f_*𝒪_X` is scheme-theoretically dominant**: on the sections over
every open `U` the isomorphism `𝒪_Y ⟶ f_*𝒪_X` is the ring map `f.app U`, which is therefore
injective, so the kernel ideal sheaf of `f` vanishes. -/
theorem isSchemeTheoreticallyDominant_of_isIso_unitToPushforwardUnit (f : X ⟶ Y)
    [QuasiCompact f] [IsIso (Scheme.Modules.unitToPushforwardUnit f)] :
    IsSchemeTheoreticallyDominant f := by
  refine ⟨Scheme.IdealSheafData.ext (funext fun U => ?_)⟩
  rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply,
    RingHom.ker_eq_bot_iff_eq_zero]
  intro a ha
  exact (ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.toPresheaf Y).map (Scheme.Modules.unitToPushforwardUnit f)).app
      (Opposite.op U.1))).1
    ((Scheme.Hom.app_unitToPushforwardObjUnit f U.1 a).trans (ha.trans (map_zero _).symm))

/-- **`f` is scheme-theoretically dominant over a local base, from the special fibre**, under the
hypotheses of `AlgebraicGeometry.isIso_unitToPushforwardUnit_of_specialFibre_of_isLocalRing`. -/
theorem isSchemeTheoreticallyDominant_of_specialFibre_of_isLocalRing (f : X ⟶ Y)
    (q : Y ⟶ Spec (.of Λ)) [LocallyOfFinitePresentation (f ≫ q)] [LocallyOfFinitePresentation q]
    [IsProper f] [UniversallyClosed q]
    (hflat : ∀ x : X, (f ≫ q) x = IsLocalRing.closedPoint Λ →
      IsFlatAt (f ≫ q).toLRSHom.toShHom x)
    (hdim : ∀ y : q.fiber (IsLocalRing.closedPoint Λ),
      topologicalKrullDim ((Stacks.Flatness.fiberHom f q (IsLocalRing.closedPoint Λ)).fiber y) ≤
        ((1 : ℕ) : WithBot ℕ∞))
    (hR : IsZero (firstDirectImageStructureSheaf
      (pullback.snd f (q.fiberι (IsLocalRing.closedPoint Λ)))))
    (hiso : IsIso (Scheme.Modules.unitToPushforwardUnit
      (pullback.snd f (q.fiberι (IsLocalRing.closedPoint Λ))))) :
    IsSchemeTheoreticallyDominant f :=
  have := isIso_unitToPushforwardUnit_of_specialFibre_of_isLocalRing f q hflat hdim hR hiso
  isSchemeTheoreticallyDominant_of_isIso_unitToPushforwardUnit f

/-- **Two morphisms into a separated scheme agreeing after a scheme-theoretically dominant
morphism are equal.** Let `u v : W ⟶ Y` be morphisms over `T` with `Y ⟶ T` separated, and
`d : D ⟶ W` scheme-theoretically dominant with `d ≫ u = d ≫ v`. The equalizer of `u` and `v` is
a closed subscheme of `W` (the base change of the diagonal of `Y ⟶ T`) through which `d` factors,
so its ideal sheaf lies in the kernel of `d`, which vanishes: it is all of `W`. -/
@[sga "3 IX 4.1" "partial"]
theorem eq_of_comp_eq_of_isSchemeTheoreticallyDominant {D W Y T : Scheme.{u}} (b : Y ⟶ T)
    [IsSeparated b] {u v : W ⟶ Y} (huv : u ≫ b = v ≫ b) (d : D ⟶ W)
    [IsSchemeTheoreticallyDominant d] (hd : d ≫ u = d ≫ v) : u = v := by
  let g : W ⟶ pullback b b := pullback.lift u v huv
  let e := pullback.snd (pullback.diagonal b) g
  let d' : D ⟶ pullback (pullback.diagonal b) g :=
    pullback.lift (d ≫ u) d (pullback.hom_ext
      (by rw [Category.assoc, pullback.diagonal_fst, Category.comp_id, Category.assoc,
        pullback.lift_fst])
      (by rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, Category.assoc,
        pullback.lift_snd, hd]))
  have hke : e.ker = ⊥ := by
    have h := Scheme.Hom.le_ker_comp d' e
    rw [pullback.lift_snd, d.ker_eq_bot] at h
    exact le_bot_iff.1 h
  have : IsIso e := IsClosedImmersion.isIso_iff_ker_eq_bot.2 hke
  have hc := pullback.condition (f := pullback.diagonal b) (g := g)
  have h1 : pullback.fst (pullback.diagonal b) g = e ≫ u := by
    have := congrArg (· ≫ pullback.fst b b) hc
    simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id] at this
    rw [this, pullback.lift_fst]
  have h2 : pullback.fst (pullback.diagonal b) g = e ≫ v := by
    have := congrArg (· ≫ pullback.snd b b) hc
    simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id] at this
    rw [this, pullback.lift_snd]
  exact (cancel_epi e).1 (h1.symm.trans h2)

/-- **A morphism of base changes compatible with a scheme-theoretically dominant morphism
descends.** Let `π : T ⟶ S` be surjective, flat and quasi-compact, `X`, `Y₁`, `Y₂` schemes over
`S` with `Y₂` separated, and `cᵢ : X ⟶ Yᵢ` over `S` with `c₁` quasi-compact and
scheme-theoretically dominant. A morphism `ψ₀ : Y₁,T ⟶ Y₂,T` over `T` with `c₁,T ≫ ψ₀ = c₂,T`
is the base change of a morphism `ψ : Y₁ ⟶ Y₂` over `S`, and then `c₁ ≫ ψ = c₂`.

The descent condition of Stacks 040L holds because the two pullbacks of `ψ₀` to
`Y₁,T ×_{Y₁} Y₁,T` agree after the base change of `c₁` to it, which is scheme-theoretically
dominant (flat base change), and `Y₂` is separated. -/
theorem exists_desc_of_isSchemeTheoreticallyDominant {S T X Y₁ Y₂ : Scheme.{u}} (π : T ⟶ S)
    [Flat π] [Surjective π] [QuasiCompact π] {fX : X ⟶ S} {fY₁ : Y₁ ⟶ S} {fY₂ : Y₂ ⟶ S}
    [IsSeparated fY₂] (c₁ : X ⟶ Y₁) (hc₁ : c₁ ≫ fY₁ = fX) [IsSchemeTheoreticallyDominant c₁]
    [QuasiCompact c₁] (c₂ : X ⟶ Y₂) (hc₂ : c₂ ≫ fY₂ = fX)
    (ψ₀ : pullback fY₁ π ⟶ pullback fY₂ π)
    (hover : ψ₀ ≫ pullback.snd fY₂ π = pullback.snd fY₁ π)
    (hψ₀ : pullback.map fX π fY₁ π c₁ (𝟙 T) (𝟙 S) (by simp [hc₁]) (by simp) ≫ ψ₀ =
      pullback.map fX π fY₂ π c₂ (𝟙 T) (𝟙 S) (by simp [hc₂]) (by simp)) :
    ∃ ψ : Y₁ ⟶ Y₂, ψ ≫ fY₂ = fY₁ ∧ pullback.fst fY₁ π ≫ ψ = ψ₀ ≫ pullback.fst fY₂ π ∧
      c₁ ≫ ψ = c₂ := by
  set m₁ := pullback.map fX π fY₁ π c₁ (𝟙 T) (𝟙 S) (by simp [hc₁]) (by simp)
  set m₂ := pullback.map fX π fY₂ π c₂ (𝟙 T) (𝟙 S) (by simp [hc₂]) (by simp)
  have hψ : m₁ ≫ ψ₀ ≫ pullback.fst fY₂ π = m₂ ≫ pullback.fst fY₂ π := by
    rw [← Category.assoc, hψ₀]
  have hb : ∀ {A : Scheme.{u}} (j : A ⟶ pullback fY₁ π),
      (j ≫ ψ₀ ≫ pullback.fst fY₂ π) ≫ fY₂ = (j ≫ pullback.fst fY₁ π) ≫ fY₁ := by
    intro A j
    simp only [Category.assoc]
    rw [pullback.condition (f := fY₂), reassoc_of% hover, ← pullback.condition]
  have key : ∀ {Z : Scheme.{u}} (g : Z ⟶ Y₁) (j : Z ⟶ pullback fY₁ π),
      j ≫ pullback.fst fY₁ π = g →
      pullback.snd c₁ g ≫ j ≫ ψ₀ ≫ pullback.fst fY₂ π = pullback.fst c₁ g ≫ c₂ := by
    intro Z g j hj
    have hcond : pullback.fst c₁ g ≫ fX = (pullback.snd c₁ g ≫ j ≫ pullback.snd fY₁ π) ≫ π := by
      have e2 : g ≫ fY₁ = j ≫ pullback.snd fY₁ π ≫ π := by
        rw [← hj, Category.assoc, pullback.condition]
      rw [← hc₁, ← Category.assoc, pullback.condition (f := c₁), Category.assoc, e2]
      simp only [Category.assoc]
    let x := pullback.lift _ _ hcond
    have hx : x ≫ m₁ = pullback.snd c₁ g ≫ j := by
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
          pullback.condition (f := c₁)]
        exact congrArg (_ ≫ ·) hj.symm
      · rw [Category.assoc, pullback.lift_snd, Category.comp_id, pullback.lift_snd,
          Category.assoc]
    calc _ = (x ≫ m₁) ≫ ψ₀ ≫ pullback.fst fY₂ π := by rw [hx, Category.assoc]
      _ = x ≫ m₂ ≫ pullback.fst fY₂ π := by rw [Category.assoc, hψ]
      _ = _ := by rw [pullback.lift_fst, pullback.lift_fst_assoc]
  have hcan : pullback.fst (pullback.fst fY₁ π) (pullback.fst fY₁ π) ≫ ψ₀ ≫
        pullback.fst fY₂ π =
      pullback.snd (pullback.fst fY₁ π) (pullback.fst fY₁ π) ≫ ψ₀ ≫ pullback.fst fY₂ π :=
    eq_of_comp_eq_of_isSchemeTheoreticallyDominant fY₂
      ((hb _).trans ((congrArg (· ≫ fY₁) pullback.condition).trans (hb _).symm))
      (pullback.snd c₁ (pullback.fst (pullback.fst fY₁ π) (pullback.fst fY₁ π) ≫
        pullback.fst fY₁ π))
      ((key _ _ rfl).trans (key _ _ pullback.condition.symm).symm)
  obtain ⟨ψ, ⟨hψ₁, hψ₂⟩, -⟩ :=
    existsUnique_desc_of_surjective_flat_quasiCompact π fY₁ fY₂ ψ₀ hover hcan
  refine ⟨ψ, hψ₁, hψ₂, eq_of_comp_eq_of_surjective_of_flat (pullback.fst fX π) ?_⟩
  calc pullback.fst fX π ≫ c₁ ≫ ψ
      = m₁ ≫ pullback.fst fY₁ π ≫ ψ := by rw [pullback.lift_fst_assoc, Category.assoc]
    _ = pullback.fst fX π ≫ c₂ := by rw [hψ₂, hψ, pullback.lift_fst]

/-- **An isomorphism of base changes compatible with a scheme-theoretically dominant morphism
descends to an isomorphism.** Under the hypotheses of
`AlgebraicGeometry.exists_desc_of_isSchemeTheoreticallyDominant`, if `ψ₀` is an isomorphism, so is
the descended morphism `ψ : Y₁ ⟶ Y₂`: its base change along the surjective flat quasi-compact
`π` is `ψ₀`, and isomorphisms descend along such morphisms (Stacks 02L4). -/
theorem exists_iso_desc_of_isSchemeTheoreticallyDominant {S T X Y₁ Y₂ : Scheme.{u}}
    (π : T ⟶ S) [Flat π] [Surjective π] [QuasiCompact π] {fX : X ⟶ S} {fY₁ : Y₁ ⟶ S}
    {fY₂ : Y₂ ⟶ S} [IsSeparated fY₂] (c₁ : X ⟶ Y₁) (hc₁ : c₁ ≫ fY₁ = fX)
    [IsSchemeTheoreticallyDominant c₁] [QuasiCompact c₁] (c₂ : X ⟶ Y₂) (hc₂ : c₂ ≫ fY₂ = fX)
    (ψ₀ : pullback fY₁ π ≅ pullback fY₂ π)
    (hover : ψ₀.hom ≫ pullback.snd fY₂ π = pullback.snd fY₁ π)
    (hψ₀ : pullback.map fX π fY₁ π c₁ (𝟙 T) (𝟙 S) (by simp [hc₁]) (by simp) ≫ ψ₀.hom =
      pullback.map fX π fY₂ π c₂ (𝟙 T) (𝟙 S) (by simp [hc₂]) (by simp)) :
    ∃ ψ : Y₁ ≅ Y₂, ψ.hom ≫ fY₂ = fY₁ ∧
      pullback.fst fY₁ π ≫ ψ.hom = ψ₀.hom ≫ pullback.fst fY₂ π ∧ c₁ ≫ ψ.hom = c₂ := by
  obtain ⟨ψ, hψ₁, hψ₂, hψ₃⟩ :=
    exists_desc_of_isSchemeTheoreticallyDominant π c₁ hc₁ c₂ hc₂ ψ₀.hom hover hψ₀
  have hs : IsPullback (ψ₀.hom ≫ pullback.snd fY₂ π) (pullback.fst fY₁ π) π (ψ ≫ fY₂) := by
    rw [hover, hψ₁]
    exact (IsPullback.of_hasPullback fY₁ π).flip
  have hpb : IsPullback ψ₀.hom (pullback.fst fY₁ π) (pullback.fst fY₂ π) ψ :=
    IsPullback.of_right hs hψ₂.symm (IsPullback.of_hasPullback fY₂ π).flip
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      (pullback.fst fY₂ π) := ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have hiso : MorphismProperty.isomorphisms Scheme.{u} ψ :=
    MorphismProperty.of_isPullback_of_descendsAlong hpb hQ
      (show IsIso ψ₀.hom from inferInstance)
  have : IsIso ψ := hiso
  exact ⟨asIso ψ, hψ₁, hψ₂, hψ₃⟩

end AlgebraicGeometry
