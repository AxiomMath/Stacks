module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.LocalNilpotentLift
public import StacksFrontier.Deformation.Artin.RimSchlessinger.AlgebraicStack
public import StacksFrontier.Deformation.Artin.RimSchlessinger.FormallySmoothCocone
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.FormallySmoothOnObjects
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersection
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Artin.RimSchlessinger

/-!
# Condition (RS) for an algebraic stack

This file proves [Stacks Project, Tag 07WQ]: an algebraic stack `𝒳` over `S` satisfies the
Rim–Schlessinger condition (RS) of [Stacks Project, Tag 07WP].

Fix a pushout `Y' = Y ⨿_X X'` of spectra of Artinian local rings of finite type over `S` along a
closed immersion `X ⟶ X'`. Full faithfulness of the comparison `𝒳_{Y'} ⟶ 𝒳_Y ×_{𝒳_X} 𝒳_{X'}`
comes from the representable diagonal. For essential surjectivity, a span of `𝒳` over the square
is given a cocone through the smooth presentation `P : (Sch/U) ⟶ 𝒳`, as in
`Deformation.Artin.nonempty_cocone_of_atlas_of_hasLiftsAlong`: étale-locally on `Y'` the object
over `Y` comes from `U`, and the lift has to be carried across the base change `X_k ⟶ X'_k` of
the closed immersion. That base change is a thickening, possibly of higher order, into an affine
scheme étale, hence finite, over the Artinian local `X'`.

So the input from the presentation is lifting along closed immersions with nilpotent kernel into
affine test objects whose global sections are finite over a local ring with nilpotent maximal
ideal. The first-order case is formal smoothness on objects against that class of test objects,
which a smooth morphism of algebraic spaces has without the torsor argument of Stacks 04AM
(`AlgebraicGeometry.Space.formallySmoothOn_hasFiniteLocalNilpotentSections_of_isSmooth`), carried
to the presentation by Stacks 06D3. The thickening is then factored into first-order steps
through spectra of quotients.

## Main results

* `AlgebraicGeometry.Stack.hasLiftsAlong_specOverHom_of_isNilpotent` and
  `AlgebraicGeometry.Stack.hasLiftsAlong_of_isNilpotent`: lifts along thickenings with nilpotent
  kernel, from formal smoothness on objects against finite test objects.
* `Deformation.Artin.isThickening_of_surjective_appTop_of_isArtinianRing`: a closed immersion into
  the spectrum of an Artinian local ring is a thickening.
* `Deformation.Artin.satisfiesRS_of_isAlgebraicStack`: **Stacks 07WQ**.

## Implementation notes

The source deduces 07WQ from Stacks 07WN, which builds the object over `Y'` by pushing out
algebraic spaces. Here the pushout is taken only in the slice category over the scheme `U`, where
it is a pushout of schemes, and the algebraic spaces enter only through the lifting property of
the presentation. No Noetherian hypothesis on `S` is needed.

## References

* [Stacks Project, Tag 07WQ](https://stacks.math.columbia.edu/tag/07WQ)
* [Stacks Project, Tag 07WP](https://stacks.math.columbia.edu/tag/07WP)
* [Stacks Project, Tag 07WN](https://stacks.math.columbia.edu/tag/07WN)
* [Stacks Project, Tag 06D3](https://stacks.math.columbia.edu/tag/06D3)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
  IsLocalRing

universe u v w

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Lifts along thickenings with nilpotent kernel -/

/-- **Lifts along a thickening of spectra with nilpotent kernel.** Let `P` be formally smooth on
objects for the larger test objects whose global sections are finite over a local ring with
nilpotent maximal ideal, let `A` be a finite algebra over such a ring and `A ⟶ A₀` a surjection
with nilpotent kernel, both algebras over a ring `R'` with `Spec R' ⟶ S` fixed. Then `P` has lifts
along `Spec A₀ ⟶ Spec A`: the thickening is a composite of first-order thickenings of spectra of
quotients of `A`. -/
theorem hasLiftsAlong_specOverHom_of_isNilpotent
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} {P : 𝒳 ⟶ 𝒴}
    (hP : IsFormallySmoothOnObjectsOn B S hS (Space.HasFiniteLocalNilpotentSections B S hS) 𝒳 𝒴 P)
    (R₀ : Type u) [CommRing R₀] [IsLocalRing R₀] (hR₀ : IsNilpotent (maximalIdeal R₀))
    {R' : Type u} [CommRing R'] (s₀ : Spec (.of R') ⟶ S) (n : ℕ) :
    ∀ {A A₀ : Type u} [CommRing A] [CommRing A₀] [Algebra R₀ A] [Module.Finite R₀ A]
      [Algebra R' A] [Algebra R' A₀] [Algebra A A₀] [IsScalarTower R' A A₀],
      Function.Surjective (algebraMap A A₀) →
      RingHom.ker (algebraMap A A₀) ^ n = ⊥ →
      ∀ (hA : B.Contains (Spec (.of A))) (hA₀ : B.Contains (Spec (.of A₀))),
        HasLiftsAlong P
          (Space.specOverHom B S hS s₀ hA hA₀ (IsScalarTower.toAlgHom R' A A₀)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A A₀ _ _ _ _ _ _ _ _ hπ hn hA hA₀
  by_cases h2 : n ≤ 2
  · intro x y' φ hφ
    have := hφ
    refine hP.exists_lift _ (inferInstanceAs (IsAffine (Spec (.of A₀))))
      (inferInstanceAs (IsAffine (Spec (.of A))))
      (Space.hasFiniteLocalNilpotentSections_specOver B S hS s₀ R₀ hR₀ A hA) ?_ φ
    exact Stacks.Smooth.isFirstOrderThickening_specMap (CommRingCat.ofHom (algebraMap A A₀)) hπ
      (eq_bot_iff.2 ((Ideal.pow_le_pow_right h2).trans hn.le))
  push Not at h2
  -- an intermediate quotient `A₁ = A ⧸ K^(n-1)`
  set K := RingHom.ker (algebraMap A A₀) with hK
  let A₁ := A ⧸ K ^ (n - 1)
  let : Algebra A₁ A₀ := (Ideal.Quotient.lift (K ^ (n - 1)) (algebraMap A A₀) fun a ha =>
    (RingHom.mem_ker).1 (Ideal.pow_le_self (by omega) ha)).toAlgebra
  have : IsScalarTower A A₁ A₀ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R' A A₁ := inferInstance
  have : IsScalarTower R' A₁ A₀ := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R' A A₁, IsScalarTower.algebraMap_apply R' A A₀,
      IsScalarTower.algebraMap_apply A A₁ A₀]
  have : Module.Finite R₀ A₁ := inferInstance
  have hA₁ : B.Contains (Spec (.of A₁)) :=
    Scheme.size_Spec_lt_of_mk_le_max B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit hA
      ((Cardinal.mk_le_of_surjective Ideal.Quotient.mk_surjective).trans (le_max_right _ _))
  have hπ₁ : Function.Surjective (algebraMap A₁ A₀) := by
    intro a₀
    obtain ⟨a, rfl⟩ := hπ a₀
    exact ⟨Ideal.Quotient.mk _ a, rfl⟩
  have hker₁ : RingHom.ker (algebraMap A₁ A₀) = K.map (Ideal.Quotient.mk (K ^ (n - 1))) := by
    ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.mem_quotient_iff_mem_sup, sup_eq_left.2 (Ideal.pow_le_self (by omega)),
      RingHom.mem_ker, RingHom.mem_ker]
    rfl
  have h₁ := ih (n - 1) (by omega) (A := A₁) (A₀ := A₀) hπ₁ (by
    rw [hker₁, ← Ideal.map_pow, Ideal.map_quotient_self]) hA₁ hA₀
  have h₂ := ih 2 (by omega) (A := A) (A₀ := A₁) Ideal.Quotient.mk_surjective (by
      rw [show RingHom.ker (algebraMap A A₁) = K ^ (n - 1) from Ideal.mk_ker, ← pow_mul]
      exact eq_bot_iff.2 ((Ideal.pow_le_pow_right (by omega)).trans hn.le)) hA hA₁
  rw [show Space.specOverHom B S hS s₀ hA hA₀ (IsScalarTower.toAlgHom R' A A₀) =
      Space.specOverHom B S hS s₀ hA₁ hA₀ (IsScalarTower.toAlgHom R' A₁ A₀) ≫
        Space.specOverHom B S hS s₀ hA hA₁ (IsScalarTower.toAlgHom R' A A₁) by
      rw [Space.specOverHom_comp]; rfl]
  exact h₁.comp h₂

/-- **Lifts along a closed immersion with nilpotent kernel.** Let `P` be formally smooth on
objects for the larger test objects whose global sections are finite over a local ring with
nilpotent maximal ideal. Then `P` has lifts along every closed immersion `T ⟶ T'` with nilpotent
kernel into an affine such test object `T'`. -/
theorem hasLiftsAlong_of_isNilpotent
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} {P : 𝒳 ⟶ 𝒴}
    (hP : IsFormallySmoothOnObjectsOn B S hS (Space.HasFiniteLocalNilpotentSections B S hS) 𝒳 𝒴 P)
    {T T' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
    (hT' : Space.HasFiniteLocalNilpotentSections B S hS T') (i : T ⟶ T')
    (hi : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i))
    (hnil : IsNilpotent (RingHom.ker ((BigFppfOver.toScheme B S hS).map i).appTop.hom)) :
    HasLiftsAlong P i := by
  obtain ⟨R₀, _, _, _, hR₀, _⟩ := hT'
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj T) :=
    isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map i)
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj T', ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) :=
    ((BigFppfOver.toScheme B S hS).map i).appTop.hom.toAlgebra
  have hsurj : Function.Surjective (algebraMap Γ((BigFppfOver.toScheme B S hS).obj T', ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) :=
    (_root_.AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine
      ((BigFppfOver.toScheme B S hS).map i)).2
  obtain ⟨n, hn⟩ := hnil
  let eT := Space.isoSpecOver B S hS i rfl
  let eT' := Space.isoSpecOverSelf B S hS T'
  have hiT : i = eT.hom ≫ Space.specOverHom B S hS (Space.specStructure B S hS T')
      (Space.contains_spec_sections B S hS T') (Space.contains_spec_sections B S hS T)
      (IsScalarTower.toAlgHom _ _ _) ≫ eT'.inv := by
    calc i = eT.hom ≫ eT.inv ≫ i := by simp
      _ = _ := by
        rw [Space.isoSpecOver_inv_comp]
        exact congrArg (fun t => eT.hom ≫ t ≫ eT'.inv)
          (Space.specOverHom_congr (AlgHom.ext fun _ => rfl))
  rw [hiT]
  exact (hasLiftsAlong_of_isIso P eT.hom).comp
    ((hasLiftsAlong_specOverHom_of_isNilpotent hP R₀ hR₀ (Space.specStructure B S hS T') n hsurj
      (by rwa [Ideal.zero_eq_bot] at hn) _ _).comp (hasLiftsAlong_of_isIso P eT'.inv))

end AlgebraicGeometry.Stack

namespace Deformation.Artin

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The maximal ideal of an Artinian local ring is nilpotent. -/
private theorem isNilpotent_maximalIdeal_of_isArtinianRing (R : Type*) [CommRing R]
    [IsLocalRing R] [IsArtinianRing R] : IsNilpotent (maximalIdeal R) := by
  simpa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] using
    IsArtinianRing.isNilpotent_jacobson_bot (R := R)

/-- A morphism of affine schemes, surjective on global sections, into the spectrum of an Artinian
local ring from a nonempty scheme is a thickening: its kernel lies in the nilpotent maximal
ideal. -/
theorem isThickening_of_surjective_appTop_of_isArtinianRing {V V' : Scheme.{u}} [IsAffine V]
    [IsAffine V'] [IsLocalRing Γ(V', ⊤)] [IsArtinianRing Γ(V', ⊤)] [Nontrivial Γ(V, ⊤)]
    (g : V ⟶ V') (hsurj : Function.Surjective g.appTop.hom) :
    Stacks.Thickenings.IsThickening g := by
  have hci : IsClosedImmersion g := IsClosedImmersion.of_surjective_of_isAffine g hsurj
  have hne : RingHom.ker g.appTop.hom ≠ ⊤ := RingHom.ker_ne_top _
  obtain ⟨n, hn⟩ := isNilpotent_maximalIdeal_of_isArtinianRing Γ(V', ⊤)
  refine Stacks.Thickenings.isThickening_of_ker_pow_eq_bot g hci (n := n) ?_
  refine (Stacks.Smooth.ker_pow_eq_bot_iff_of_isAffine g (n + 1)).2 (eq_bot_iff.2 ?_)
  calc RingHom.ker g.appTop.hom ^ (n + 1) ≤ maximalIdeal Γ(V', ⊤) ^ (n + 1) :=
        Ideal.pow_right_mono (IsLocalRing.le_maximalIdeal hne) _
    _ ≤ maximalIdeal Γ(V', ⊤) ^ n := Ideal.pow_le_pow_right (Nat.le_succ n)
    _ = ⊥ := by rw [hn, Ideal.zero_eq_bot]

/-- **Stacks 07WQ: an algebraic stack satisfies condition (RS).** Let `𝒳` be an algebraic stack
over `S`. At every pushout `Y' = Y ⨿_X X'` of spectra of Artinian local rings of finite type over
`S` along a closed immersion `X ⟶ X'`, the comparison from the fibre over `Y'` to the two-fibre
product of the fibres over `Y` and `X'` over the fibre over `X` is an equivalence.

Full faithfulness comes from the representable diagonal alone
(`Deformation.Artin.fullyFaithful_fiberSquareComparison_of_hasRepresentableDiagonal`). For
essential surjectivity, a span of `𝒳` over the square has a cocone
(`Deformation.Artin.nonempty_cocone_of_atlas_of_hasLiftsAlong`): its object over `Y` lifts along
the smooth presentation `(Sch/U) ⟶ 𝒳` étale-locally, the étale neighbourhoods extend across the
thickening `Y ⟶ Y'`, and over each of them the lift is carried across the base change of
`X ⟶ X'`. That base change is a closed immersion with nilpotent kernel into an affine scheme
étale, hence finite, over the Artinian local `X'`, and the presentation has lifts along it
(`AlgebraicGeometry.Stack.hasLiftsAlong_of_isNilpotent`): it is formally smooth on objects
against such test objects because a smooth morphism of algebraic spaces lifts over them
(`AlgebraicGeometry.Space.formallySmoothOn_hasFiniteLocalNilpotentSections_of_isSmooth`). -/
@[stacks 07WQ]
theorem satisfiesRS_of_isAlgebraicStack (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) :
    SatisfiesRS B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids := by
  obtain ⟨h𝒳, hrest⟩ := 𝒳.property
  dsimp only at hrest
  obtain ⟨⟨hst, -⟩, -, U, f, hrep, hprop⟩ := hrest
  have hdiag := Stack.SelfIntersection.hasRepresentableDiagonal_of_isAlgebraicStack B S hS 𝒳.val
    𝒳.property
  let P : Stack.schemeFibredCategory B S hS U ⟶ 𝒳.val := Bicategory.InducedBicategory.mkHom f
  -- the presentation is formally smooth on objects against finite test objects
  have hsm : ∀ {X Y : AlgebraicSpaces B S hS} (m : X ⟶ Y), Space.IsSmooth B S hS m.hom →
      Space.FormallySmoothOn (Space.HasFiniteLocalNilpotentSections B S hS) m.hom :=
    fun {X Y} _ hm =>
      Space.formallySmoothOn_hasFiniteLocalNilpotentSections_of_isSmooth B S hS X.2 Y.2 hm
  have hFS : Stack.IsFormallySmoothOnObjectsOn B S hS (Space.HasFiniteLocalNilpotentSections B S hS)
      (Stack.schemeFibredCategory B S hS U) 𝒳.val P :=
    BigFppfOver.isFormallySmoothOnObjectsOn_of_formallySmoothOn B S hS _ P hrep
      (fun V y hy F hF hE => hsm _ (hprop V y hy F hF hE).2)
  let : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  intro X X' Y Y' i j i' j' w hX hX' hY hY' _ _ _ _ hci hpo
  let T := BigFppfOver.toScheme B S hS
  have : IsAffine (T.obj X) := hX.1
  have : IsAffine (T.obj X') := hX'.1
  have : IsAffine (T.obj Y) := hY.1
  have : IsAffine (T.obj Y') := hY'.1
  have : IsLocalRing Γ(T.obj X, ⊤) := hX.2.1
  have : IsLocalRing Γ(T.obj Y, ⊤) := hY.2.1
  have : IsLocalRing Γ(T.obj X', ⊤) := hX'.2.1
  have : IsLocalRing Γ(T.obj Y', ⊤) := hY'.2.1
  have : IsArtinianRing Γ(T.obj X', ⊤) := hX'.2.2
  have : IsArtinianRing Γ(T.obj Y', ⊤) := hY'.2.2
  -- the square of global sections is cartesian, and both legs are thickenings
  have hΓ : IsPullback (T.map j').appTop (T.map i').appTop (T.map j).appTop (T.map i).appTop := by
    simpa [T] using (hpo.map Scheme.Γ.rightOp).unop
  have hisurj : Function.Surjective (T.map i).appTop.hom :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine (T.map i)).2
  have hgt := isThickening_of_surjective_appTop_of_isArtinianRing (T.map i) hisurj
  have hit := isThickening_of_surjective_appTop_of_isArtinianRing (T.map j')
    (surjective_of_isPullback hΓ hisurj)
  let Q : BaseSquare (BigFppfOver B S hS) := ⟨X, Y, X', Y', j, i, j', i', w.symm⟩
  have : IsAffineHom (T.map j) := isAffineHom_of_isAffine _
  have hFF := fullyFaithful_fiberSquareComparison_of_hasRepresentableDiagonal B S hS 𝒳.val hdiag
    i j i' j' w hgt hpo
  have := hFF.full
  have := hFF.faithful
  -- lifts along the base changes of the thickening `X ⟶ X'`
  have hlift : ∀ (Z₁ : BigFppfOver B S hS) (τ : Z₁ ⟶ Q.Z), Etale (T.map τ) →
      IsAffine (T.obj Z₁) → Stack.HasLiftsAlong P (Q.baseChange τ).g := by
    intro Z₁ τ hτ hZ₁
    have := hτ
    have := hZ₁
    let Qk := Q.baseChange τ
    let a := Q.baseChangeHom τ
    have sX' : IsPullback (T.map Qk.j) (T.map a.aW) (T.map τ) (T.map Q.j) :=
      (Q.isPullback_baseChange_j τ).map T
    have sX'' : IsPullback (T.map Qk.g) (T.map a.aU) (T.map a.aW) (T.map Q.g) :=
      (Q.isPullback_baseChange_g τ).map T
    have : IsAffine (T.obj Qk.W) := IsAffine.of_isPullback sX'
    have : IsClosedImmersion (T.map i) := hci
    have hci' : IsClosedImmersion (T.map Qk.g) := MorphismProperty.of_isPullback sX''.flip hci
    have hthk : Stacks.Thickenings.IsThickening (T.map Qk.g) :=
      Stacks.Thickenings.isThickening_of_isPullback sX'' hgt
    have : Etale (T.map a.aW) := MorphismProperty.of_isPullback sX' hτ
    let : Algebra Γ(T.obj X', ⊤) Γ(T.obj Qk.W, ⊤) := (T.map a.aW).appTop.hom.toAlgebra
    have : Algebra.Etale Γ(T.obj X', ⊤) Γ(T.obj Qk.W, ⊤) :=
      HasRingHomProperty.appTop @Etale _ inferInstance
    have : Module.Finite Γ(T.obj X', ⊤) Γ(T.obj Qk.W, ⊤) := Module.Finite.of_quasiFinite
    have : IsArtinianRing Γ(T.obj Qk.W, ⊤) := IsArtinianRing.of_finite Γ(T.obj X', ⊤) _
    have hT' : Space.HasFiniteLocalNilpotentSections B S hS Qk.W :=
      ⟨Γ(T.obj X', ⊤), inferInstance, inferInstance, inferInstance,
        isNilpotent_maximalIdeal_of_isArtinianRing _, inferInstance⟩
    have hnil : IsNilpotent (RingHom.ker (T.map Qk.g).appTop.hom) := by
      obtain ⟨k, hk⟩ := IsNoetherianRing.isNilpotent_nilradical Γ(T.obj Qk.W, ⊤)
      refine ⟨k, le_bot_iff.1 ?_⟩
      calc RingHom.ker (T.map Qk.g).appTop.hom ^ k ≤ nilradical Γ(T.obj Qk.W, ⊤) ^ k :=
            Ideal.pow_right_mono (fun _ ha => mem_nilradical.2
              (hthk.isNilpotent_of_mem_ker_appTop ha)) k
        _ = ⊥ := by rw [hk, Ideal.zero_eq_bot]
    exact Stack.hasLiftsAlong_of_isNilpotent hFS hT' Qk.g hci' hnil
  have : (fiberSquareComparison 𝒳.val.val.p (chosenPullbacks 𝒳.val.val.p) j i j' i'
      w.symm).EssSurj :=
    essSurj_fiberSquareComparison_of_nonempty_cocone 𝒳.val.isFiberedInGroupoids _ j i j' i'
      w.symm fun s => nonempty_cocone_of_atlas_of_hasLiftsAlong B S hS 𝒳.val hst hdiag P hrep
        hprop Q hΓ hgt hit hlift s
  exact Functor.IsEquivalence.mk

end Deformation.Artin

end
