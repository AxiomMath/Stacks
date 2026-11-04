module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.NormGroupTensorChart
public import StacksFrontier.AlgebraicGeometry.Divisors.Norm.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankSections
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeProper
public import StacksFrontier.RingTheory.Norm.GaloisProduct

/-!
# The hint of Stacks 0FH9, proved

Let `π : P ⟶ Q` be finite locally free of rank `d > 0` with `P` integral, and let a finite group
`G` of order `d` act faithfully on `P` by endomorphisms over `Q`. Then the canonical norm
`Norm_π` of Tag 0BD2 satisfies, on functions,

  `π^♯ (Norm_π s) = ∏_{σ ∈ G} (a σ)^♯ s`   for every `s ∈ Γ(P, π⁻¹V)`.

This is the identity that Stacks 0FH9 gives as the hint for the computation of `π^*𝒩` it omits
(for `π : Xⁿ ⟶ Sⁿ(X)` and `G = Sₙ`). With it,
`Stacks.Divisors.hasNormGroupProductTensor_of_app_norm_eq_prod`
gives the isomorphism `π^*(Norm_π ℒ) ≅ ⨂_{σ ∈ G} (a σ)^*ℒ` for every invertible `ℒ` on `P`.

The proof is local on `Q`. Over an affine open `V` with `π⁻¹V` nonempty, `A = Γ(P, π⁻¹V)` is a
domain, finite projective of constant rank `d` over `R = Γ(Q, V)`, and `R ⟶ A` is injective
because the rank is positive. The canonical norm is `Algebra.projectiveNorm` there, the action of
`G` on `A` is faithful because two endomorphisms over the separated morphism `π` agreeing on the
dense open `π⁻¹V` agree, and `Algebra.algebraMap_projectiveNorm_eq_prod_of_algHom` applies.

## Main results

* `Stacks.Divisors.app_finiteLocallyFreeNorm_eq_prod`: the identity on functions.
* `Stacks.Divisors.hasNormGroupProductTensor_finiteLocallyFreeNormOfRank`: the tensor form of the
  hint for the canonical norm.
* `pullbackPicardClass_normInvertible_fibrePower_eq_factorial_nsmul_sum_of_faithful`
  (in `Stacks.SheafOfModules`): the resulting computation `π^*𝒩 = (n-1)! • ∑ᵢ [ℒᵢ]` on a
  fibre power, with no hint assumed.

## References

* [Stacks Project, Tag 0FH9](https://stacks.math.columbia.edu/tag/0FH9)
* [Stacks Project, Tag 0BD2](https://stacks.math.columbia.edu/tag/0BD2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Divisors

variable {P Q : Scheme.{u}}

/-- An endomorphism equal to the identity acts trivially on functions over any open. -/
private theorem appLE_apply_of_eq_id {b : P ⟶ P} (hb : b = 𝟙 P) (U : P.Opens)
    (e : U ≤ b ⁻¹ᵁ U) (x : Γ(P, U)) : (b.appLE U U e).hom x = x := by
  subst hb
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
  show (P.presheaf.map (𝟙 (op U))).hom x = x
  rw [P.presheaf.map_id]
  rfl

/-- An endomorphism equal to a composite acts on functions as the composite of the actions. -/
private theorem appLE_apply_of_eq_comp {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {b : X ⟶ Z}
    (hb : b = f ≫ g) {U : Z.Opens} {V : Y.Opens} {W : X.Opens} (e : W ≤ b ⁻¹ᵁ U)
    (e₁ : W ≤ f ⁻¹ᵁ V) (e₂ : V ≤ g ⁻¹ᵁ U) (x : Γ(Z, U)) :
    (b.appLE U W e).hom x = (f.appLE V W e₁).hom ((g.appLE U V e₂).hom x) := by
  subst hb
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

/-- Pulling back a function along an endomorphism over `π` fixes the functions coming from the
target: `(b)^♯ (π^♯ r) = π^♯ r` on `π⁻¹V`. -/
theorem appLE_app_of_comp_eq {π : P ⟶ Q} {b : P ⟶ P} (hb : b ≫ π = π) (V : Q.Opens)
    (e : π ⁻¹ᵁ V ≤ b ⁻¹ᵁ (π ⁻¹ᵁ V)) (r : Γ(Q, V)) :
    (b.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) e).hom ((π.app V).hom r) = (π.app V).hom r := by
  rw [Scheme.Hom.app_eq_appLE]
  exact (appLE_apply_of_eq_comp hb.symm le_rfl e le_rfl r).symm

/-- Two endomorphisms over a separated morphism `π` from a reduced scheme, which induce the same
map on functions over an affine dense open `π⁻¹V`, are equal. -/
theorem eq_of_appLE_eq {π : P ⟶ Q} [IsSeparated π] [IsReduced P] {b c : P ⟶ P}
    (hb : b ≫ π = π) (hc : c ≫ π = π) (V : Q.Opens) (hV : IsAffineOpen (π ⁻¹ᵁ V))
    (hdense : Dense (π ⁻¹ᵁ V : Set P))
    (eb : π ⁻¹ᵁ V ≤ b ⁻¹ᵁ (π ⁻¹ᵁ V)) (ec : π ⁻¹ᵁ V ≤ c ⁻¹ᵁ (π ⁻¹ᵁ V))
    (h : b.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) eb = c.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) ec) : b = c := by
  have := Opens.isDominant_ι hdense
  refine ext_of_isDominant_of_isSeparated π (hb.trans hc.symm) (π ⁻¹ᵁ V).ι ?_
  rw [← Scheme.Hom.resLE_comp_ι b eb, ← Scheme.Hom.resLE_comp_ι c ec]
  congr 1
  have : IsAffine (π ⁻¹ᵁ V).toScheme := hV
  apply ext_of_isAffine
  simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, h]

variable (π : P ⟶ Q) {d : ℕ} [Morphisms.IsFiniteLocallyFreeOfRank π d]
  {G : Type*} [Group G] [Fintype G] (a : G → (P ⟶ P)) (ha : ∀ σ, a σ ≫ π = π)

/-- The identity on functions over an affine open of the target. -/
theorem app_finiteLocallyFreeNorm_eq_prod_of_isAffineOpen [IsIntegral P]
    (h1 : a 1 = 𝟙 P) (hmul : ∀ σ τ, a (σ * τ) = a σ ≫ a τ) (hinj : Function.Injective a)
    (hd : Fintype.card G = d) (hpos : 0 < d) (V : Q.Opens) (hV : IsAffineOpen V)
    (s : Γ(P, π ⁻¹ᵁ V)) :
    letI := Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree π d
    (π.app V).hom ((finiteLocallyFreeNorm π).app V s) =
      ∏ σ : G, ((a σ).appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V)
        (le_of_eq (preimage_preimage_of_comp_eq (ha σ) V).symm)).hom s := by
  let := Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree π d
  rcases (π ⁻¹ᵁ V : Set P).eq_empty_or_nonempty with hempty | hne
  · have : Subsingleton Γ(P, π ⁻¹ᵁ V) :=
      CommRingCat.subsingleton_of_isTerminal (P.sheaf.isTerminalOfEqEmpty (SetLike.ext' hempty))
    exact Subsingleton.elim _ _
  have : Nonempty (π ⁻¹ᵁ V) := hne.to_subtype
  let := (π.app V).hom.toAlgebra
  let : (Morphisms.pushforwardStructureSheaf π).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom π _
  obtain ⟨hfin, hproj⟩ := AlgebraicGeometry.SheafOfModules.module_finite_and_projective_sections
    (Morphisms.pushforwardStructureSheaf π) ⟨V, hV⟩
  have hrank := AlgebraicGeometry.SheafOfModules.rankAtStalk_sections
    (Morphisms.pushforwardStructureSheaf π) d ⟨V, hV⟩
  have : Module.Finite Γ(Q, V) Γ(P, π ⁻¹ᵁ V) := hfin
  have : Module.Projective Γ(Q, V) Γ(P, π ⁻¹ᵁ V) := hproj
  have : FaithfulSMul Γ(Q, V) Γ(P, π ⁻¹ᵁ V) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (Module.rankAtStalk_pos_iff_algebraMap_injective.mp fun p ↦ (hrank p).symm ▸ hpos)
  -- the action on functions, as algebra maps over `Γ(Q, V)`
  let e : ∀ σ, π ⁻¹ᵁ V ≤ a σ ⁻¹ᵁ (π ⁻¹ᵁ V) := fun σ ↦
    le_of_eq (preimage_preimage_of_comp_eq (ha σ) V).symm
  let φ : G → (Γ(P, π ⁻¹ᵁ V) →ₐ[Γ(Q, V)] Γ(P, π ⁻¹ᵁ V)) := fun σ ↦
    { ((a σ).appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (e σ)).hom with
      commutes' := fun r ↦ appLE_app_of_comp_eq (ha σ) V (e σ) r }
  have hφ1 : φ 1 = AlgHom.id _ _ := AlgHom.ext fun x ↦ appLE_apply_of_eq_id h1 _ _ x
  have hφmul : ∀ σ τ, φ (σ * τ) = (φ σ).comp (φ τ) := fun σ τ ↦
    AlgHom.ext fun x ↦ appLE_apply_of_eq_comp (hmul σ τ) _ (e σ) (e τ) x
  have hφinj : Function.Injective φ := fun σ τ hστ ↦ hinj <|
    eq_of_appLE_eq (ha σ) (ha τ) V (hV.preimage π) (IsOpen.dense (π ⁻¹ᵁ V).isOpen hne)
      (e σ) (e τ) (by ext x; exact DFunLike.congr_fun hστ x)
  rw [finiteLocallyFreeNorm_app_affine_eq_projectiveNorm π ⟨V, hV⟩ hfin hproj s]
  exact Algebra.algebraMap_projectiveNorm_eq_prod_of_algHom φ hφ1 hφmul hφinj
    (fun p ↦ (hrank p).trans hd.symm) s

/-- **The hint of Stacks 0FH9.** Let `π : P ⟶ Q` be finite locally free of rank `d > 0` with `P`
integral, and let `a : G → (P ⟶ P)` be a faithful action over `Q` of a finite group of order `d`
(`a 1 = 𝟙`, `a (σ * τ) = a σ ≫ a τ`, `a` injective, `a σ ≫ π = π`). Then the canonical norm of
Tag 0BD2, composed with `π^♯`, is the product of the translates:

  `π^♯ (Norm_π s) = ∏_{σ ∈ G} (a σ)^♯ s`   for every `s ∈ Γ(P, π⁻¹V)`. -/
theorem app_finiteLocallyFreeNorm_eq_prod [IsIntegral P]
    (h1 : a 1 = 𝟙 P) (hmul : ∀ σ τ, a (σ * τ) = a σ ≫ a τ) (hinj : Function.Injective a)
    (hd : Fintype.card G = d) (hpos : 0 < d) (V : Q.Opens) (s : Γ(P, π ⁻¹ᵁ V)) :
    (π.app V).hom ((finiteLocallyFreeNormOfRank π d hpos).1.app V s) =
      ∏ σ : G, ((a σ).appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V)
        (le_of_eq (preimage_preimage_of_comp_eq (ha σ) V).symm)).hom s := by
  let := Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree π d
  show (π.app V).hom ((finiteLocallyFreeNorm π).app V s) = _
  refine P.sheaf.eq_of_locally_eq' (fun W : {W : Q.affineOpens // W.1 ≤ V} ↦ π ⁻¹ᵁ W.1.1)
    (π ⁻¹ᵁ V) (fun W ↦ homOfLE ((Opens.map π.base).map (homOfLE W.2)).le) ?_ _ _ ?_
  · intro x hx
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
      Q.isBasis_affineOpens.exists_subset_of_mem_open (show π.base x ∈ (V : Set Q) from hx)
        V.isOpen
    exact Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, hWV⟩, hxW⟩
  · rintro ⟨⟨W, hW⟩, hWV⟩
    let i : W ⟶ V := homOfLE hWV
    have hnat : ∀ t : Γ(Q, V), (P.presheaf.map ((Opens.map π.base).map i).op).hom
        ((π.app V).hom t) = (π.app W).hom ((Q.presheaf.map i.op).hom t) := fun t ↦ by
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
      rfl
    show (P.presheaf.map ((Opens.map π.base).map i).op).hom _ =
      (P.presheaf.map ((Opens.map π.base).map i).op).hom _
    rw [hnat, ← (finiteLocallyFreeNorm π).naturality i s,
      app_finiteLocallyFreeNorm_eq_prod_of_isAffineOpen π a ha h1 hmul hinj hd hpos W hW,
      map_prod]
    refine Finset.prod_congr rfl fun σ _ ↦ ?_
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map,
      Scheme.Hom.map_appLE]

include ha in
/-- **The hint of Stacks 0FH9, as an isomorphism of invertible modules.** Under the hypotheses of
`Stacks.Divisors.app_finiteLocallyFreeNorm_eq_prod`, for every invertible `ℒ` on `P`,

  `π^*(Norm_π ℒ) ≅ ⨂_{σ ∈ G} (a σ)^*ℒ`,

with `Norm_π` the canonical norm of Tag 0BD2. -/
theorem hasNormGroupProductTensor_finiteLocallyFreeNormOfRank [IsIntegral P]
    (h1 : a 1 = 𝟙 P) (hmul : ∀ σ τ, a (σ * τ) = a σ ≫ a τ) (hinj : Function.Injective a)
    (hd : Fintype.card G = d) (hpos : 0 < d) :
    haveI := Morphisms.isFinite_of_isFiniteLocallyFreeOfRank π d
    HasNormGroupProductTensor π (finiteLocallyFreeNormOfRank π d hpos).1 a :=
  have := Morphisms.isFinite_of_isFiniteLocallyFreeOfRank π d
  hasNormGroupProductTensor_of_app_norm_eq_prod π _ a ha
    (app_finiteLocallyFreeNorm_eq_prod π a ha h1 hmul hinj hd hpos)

end Stacks.Divisors

namespace Stacks.SheafOfModules

open Stacks.Scheme Nat RingedSpaceModuleAdjunction CategoryTheory.Limits

/-- **The computation `π^*𝒩 = (ℒ₁ ⊗ ⋯ ⊗ ℒₙ)^{⊗(n-1)!}` of Stacks 0FH9, without the hint as a
hypothesis.** Let `Yⁿ` be the `n`-fold fibre power of `Y` over `S`, integral, and let
`π : Yⁿ ⟶ Q` be finite locally free of rank `n!`, invariant under permuting the factors, with the
permutation action faithful. For a family `ℒᵢ` with `[ℒᵢ] = prᵢ^*[ℳ]` and the canonical norm of
Tag 0BD2,

  `π^*(Norm_π ℒ_{i₀}) = (n-1)! • ∑ᵢ [ℒᵢ]`   in   `Pic(Yⁿ)`.

The hint of the source is
`Stacks.Divisors.hasNormGroupProductTensor_finiteLocallyFreeNormOfRank`. -/
theorem pullbackPicardClass_normInvertible_fibrePower_eq_factorial_nsmul_sum_of_faithful
    {S : Scheme.{u}} (Y : Over S) {n : ℕ} {Q : Scheme.{u}}
    (π : (∏ᶜ fun _ : Fin n => Y).left ⟶ Q) [Morphisms.IsFiniteLocallyFreeOfRank π n !]
    [IsFinite π] [IsIntegral (∏ᶜ fun _ : Fin n => Y).left]
    (hinv : ∀ σ : Equiv.Perm (Fin n), (fibrePowerPerm Y n σ).left ≫ π = π)
    (hfaithful : Function.Injective fun σ : Equiv.Perm (Fin n) => (fibrePowerPerm Y n σ).left)
    (i₀ : Fin n)
    (M : SheafOfModules.{u} (structureSheafRing Y.left.toRingedSpace))
    (hM : IsInvertible Y.left.presheaf Y.left.ringCatIsSheaf M)
    (L : Fin n → SheafOfModules.{u}
      (structureSheafRing (∏ᶜ fun _ : Fin n => Y).left.toRingedSpace))
    (hL : ∀ i, IsInvertible (∏ᶜ fun _ : Fin n => Y).left.presheaf
      (∏ᶜ fun _ : Fin n => Y).left.ringCatIsSheaf (L i))
    (hpull : ∀ i, pullbackPicardClass (Pi.π (fun _ : Fin n => Y) i).left M hM =
      picardClass (∏ᶜ fun _ : Fin n => Y).left.presheaf
        (∏ᶜ fun _ : Fin n => Y).left.ringCatIsSheaf (L i) (hL i)) :
    pullbackPicardClass π (Stacks.Divisors.normInvertible π
        (Stacks.Divisors.finiteLocallyFreeNormOfRank π n ! (factorial_pos n)).1.toMorphismNormMap
        (L i₀))
        (Stacks.Divisors.isInvertible_normInvertible π _ (L i₀)
          (Stacks.Divisors.hasTrivializingTargetCover_of_isFinite_of_isInvertible π (L i₀)
            (hL i₀))) =
      (n - 1)! • ∑ i, picardClass (∏ᶜ fun _ : Fin n => Y).left.presheaf
        (∏ᶜ fun _ : Fin n => Y).left.ringCatIsSheaf (L i) (hL i) :=
  pullbackPicardClass_normInvertible_fibrePower_eq_factorial_nsmul_sum_of_tensor Y π _ i₀ M hM L
    hL hpull
    (Stacks.Divisors.hasNormGroupProductTensor_finiteLocallyFreeNormOfRank π _ hinv
      (by rw [fibrePowerPerm_one]; rfl)
      (fun σ τ ↦ by rw [← fibrePowerPerm_comp]; rfl) hfaithful
      (by rw [Fintype.card_perm, Fintype.card_fin]) (factorial_pos n))

end Stacks.SheafOfModules

end
