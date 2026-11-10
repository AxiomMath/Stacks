module

public import StacksFrontier.AlgebraicGeometry.Scheme.SquareZeroLiftAffineCombination
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Etale

/-!
# A Galois-invariant infinitesimal lift through an étale chart

Let `T ⊆ T'` be the thickening of the spectrum of a local ring `B'` defined by an ideal `J` with
`J ^ 2 = 0`, presented in the big fppf site of a scheme `S`, and let a finite group `G` act on
`B'` by automorphisms preserving `J`, hence on `T'` and `T`. Let `X` be a presheaf on the site
with an étale representable chart `a : h_U ⟶ X`, and `ψ : U ⟶ V` a morphism of the site; a
lifting problem is a section `x` of `X` over `T` invariant under `G` together with a
`G`-invariant `y : T' ⟶ V`. Suppose the problem has one solution *through the chart*: a morphism
`ℓ₀ : T' ⟶ U` restricting on `T` to a chart point of `x`, with `ℓ₀ ≫ ψ = y`.

If some `c ∈ B'` has `∑_σ σ(c) = 1`, then the problem has a solution in `X` over `T'` which is
invariant under `G`. This is the Galois averaging step of the proof of Stacks 04AM in the case of
an Artinian base, written without the cotangent complex: the solutions are an affine space,
through the canonical affine combinations of
`StacksFrontier/AlgebraicGeometry/Scheme/SquareZeroLiftAffineCombination.lean`, and the averaged
lift `∑_τ τ(c) · τℓ₀` is invariant.

## Main definitions

* `AlgebraicGeometry.Space.GaloisLift.siteComb`: the affine combination of a family of
  morphisms `T' ⟶ Z` of the site agreeing on `T`.

## Main results

* `AlgebraicGeometry.Space.GaloisLift.exists_invariant_lift`: the invariant solution.

## Implementation notes

The action of `σ` on the solutions *through the chart* is not precomposition with `σ`, which
moves the chart point; it is precomposition followed by the unique re-lift through the chart at
the original chart point, which the chart provides because it is formally étale
(`AlgebraicGeometry.Space.formallyEtale_of_etale`). That this re-lift commutes with affine
combinations is read off the self-fibre product of the chart: two families of solutions with the
same image in `X` assemble into a family of morphisms into `U ×_X U`, whose affine combination
projects to the two affine combinations.
-/

@[expose] public section

open CategoryTheory Opposite IsLocalRing

universe u

namespace AlgebraicGeometry.Space.GaloisLift

open AlgebraicGeometry.SquareZeroLift

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {R : CommRingCat.{u}} [IsLocalRing R] {J : Ideal R} (hJ : J ^ 2 = ⊥)
  {T T' : BigFppfOver B S hS}
  (e : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of (R ⧸ J)))
  (e' : (BigFppfOver.toScheme B S hS).obj T' ≅ Spec R)
  (i : T ⟶ T') (hi : (BigFppfOver.toScheme B S hS).map i = e.hom ≫ reduction J ≫ e'.inv)

include hi in
omit [IsLocalRing R] in
/-- Two morphisms out of `T'` agreeing on `T` agree on the reduction of the presentation. -/
theorem reduction_comp_eq {Z : BigFppfOver B S hS} {ℓ ℓ' : T' ⟶ Z}
    (h : i ≫ ℓ = i ≫ ℓ') :
    reduction J ≫ e'.inv ≫ (BigFppfOver.toScheme B S hS).map ℓ =
      reduction J ≫ e'.inv ≫ (BigFppfOver.toScheme B S hS).map ℓ' := by
  have hr : reduction J ≫ e'.inv = e.inv ≫ (BigFppfOver.toScheme B S hS).map i := by
    rw [hi]
    simp
  calc reduction J ≫ e'.inv ≫ (BigFppfOver.toScheme B S hS).map ℓ
      = (reduction J ≫ e'.inv) ≫ (BigFppfOver.toScheme B S hS).map ℓ := (Category.assoc _ _ _).symm
    _ = e.inv ≫ (BigFppfOver.toScheme B S hS).map (i ≫ ℓ) := by
        rw [hr, Category.assoc, Functor.map_comp]
    _ = e.inv ≫ (BigFppfOver.toScheme B S hS).map (i ≫ ℓ') := by rw [h]
    _ = reduction J ≫ e'.inv ≫ (BigFppfOver.toScheme B S hS).map ℓ' := by
        rw [Functor.map_comp, ← Category.assoc, ← hr, Category.assoc]

variable {ι : Type*} [Fintype ι]

include hJ hi in
omit [Fintype ι] in
/-- A family of morphisms out of `T'` agreeing on `T` sends the closed point to one point. -/
theorem apply_closedPoint_eq_of_agree {Z : BigFppfOver B S hS} (ℓ : ι → (T' ⟶ Z))
    (i₀ : ι) (hag : ∀ k, i ≫ ℓ k = i ≫ ℓ i₀) (k : ι) :
    (e'.inv ≫ (BigFppfOver.toScheme B S hS).map (ℓ k)) (closedPoint R) =
      (e'.inv ≫ (BigFppfOver.toScheme B S hS).map (ℓ i₀)) (closedPoint R) := by
  rw [← apply_closedPoint_eq J hJ, ← apply_closedPoint_eq J hJ (e'.inv ≫ _),
    reduction_comp_eq e e' i hi (hag k)]

/-- **The affine combination of a family of morphisms `T' ⟶ Z` of the site agreeing on `T`**,
with coefficients in `R` summing to `1`: `AlgebraicGeometry.SquareZeroLift.affineComb` of the
underlying morphisms of schemes, read through the presentation of `T'`, at the common image `z`
of the closed point. -/
noncomputable def siteComb {Z : BigFppfOver B S hS} (ℓ : ι → (T' ⟶ Z))
    (z : (BigFppfOver.toScheme B S hS).obj Z)
    (hz : ∀ k, (e'.inv ≫ (BigFppfOver.toScheme B S hS).map (ℓ k)) (closedPoint R) = z)
    (c : ι → R) (hc : ∑ k, c k = 1) (i₀ : ι) (hag : ∀ k, i ≫ ℓ k = i ≫ ℓ i₀) : T' ⟶ Z :=
  Over.homMk (B.inclusion.preimage (e'.hom ≫ affineComb J hJ
      (fun k => e'.inv ≫ (BigFppfOver.toScheme B S hS).map (ℓ k)) z hz c hc i₀
      (fun k => reduction_comp_eq e e' i hi (hag k))))
    (by
      apply B.inclusion.map_injective
      rw [Functor.map_comp, B.inclusion.map_preimage, Category.assoc,
        affineComb_comp_eq (m := e'.inv ≫ B.inclusion.map T'.hom)
          (hm := fun k => by
            rw [Category.assoc]
            change e'.inv ≫ B.inclusion.map (ℓ k).left ≫ B.inclusion.map Z.hom = _
            rw [← B.inclusion.map_comp, Over.w])]
      simp)

/-- The underlying morphism of schemes of `AlgebraicGeometry.Space.GaloisLift.siteComb`. -/
theorem toScheme_map_siteComb {Z : BigFppfOver B S hS} (ℓ : ι → (T' ⟶ Z))
    (z : (BigFppfOver.toScheme B S hS).obj Z)
    (hz : ∀ k, (e'.inv ≫ (BigFppfOver.toScheme B S hS).map (ℓ k)) (closedPoint R) = z)
    (c : ι → R) (hc : ∑ k, c k = 1) (i₀ : ι) (hag : ∀ k, i ≫ ℓ k = i ≫ ℓ i₀) :
    (BigFppfOver.toScheme B S hS).map (siteComb hJ e e' i hi ℓ z hz c hc i₀ hag) =
      e'.hom ≫ affineComb J hJ
        (fun k => e'.inv ≫ (BigFppfOver.toScheme B S hS).map (ℓ k)) z hz c hc i₀
        (fun k => reduction_comp_eq e e' i hi (hag k)) :=
  B.inclusion.map_preimage _

variable {hJ e e' i hi}

/-- **An affine combination agrees with the family on `T`.** -/
theorem comp_siteComb {Z : BigFppfOver B S hS} (ℓ : ι → (T' ⟶ Z))
    (z : (BigFppfOver.toScheme B S hS).obj Z)
    (hz : ∀ k, (e'.inv ≫ (BigFppfOver.toScheme B S hS).map (ℓ k)) (closedPoint R) = z)
    (c : ι → R) (hc : ∑ k, c k = 1) (i₀ : ι) (hag : ∀ k, i ≫ ℓ k = i ≫ ℓ i₀) :
    i ≫ siteComb hJ e e' i hi ℓ z hz c hc i₀ hag = i ≫ ℓ i₀ := by
  apply (BigFppfOver.toScheme B S hS).map_injective
  rw [Functor.map_comp, Functor.map_comp, toScheme_map_siteComb, hi]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [reduction_comp_affineComb]

/-- **Affine combinations commute with postcomposition.** -/
theorem siteComb_comp {Z W : BigFppfOver B S hS} (ℓ : ι → (T' ⟶ Z))
    (z : (BigFppfOver.toScheme B S hS).obj Z)
    (hz : ∀ k, (e'.inv ≫ (BigFppfOver.toScheme B S hS).map (ℓ k)) (closedPoint R) = z)
    (c : ι → R) (hc : ∑ k, c k = 1) (i₀ : ι) (hag : ∀ k, i ≫ ℓ k = i ≫ ℓ i₀) (g : Z ⟶ W)
    (hz' : ∀ k, (e'.inv ≫ (BigFppfOver.toScheme B S hS).map (ℓ k ≫ g)) (closedPoint R) =
      (BigFppfOver.toScheme B S hS).map g z)
    (hag' : ∀ k, i ≫ ℓ k ≫ g = i ≫ ℓ i₀ ≫ g) :
    siteComb hJ e e' i hi ℓ z hz c hc i₀ hag ≫ g =
      siteComb hJ e e' i hi (fun k => ℓ k ≫ g) _ hz' c hc i₀ hag' := by
  apply (BigFppfOver.toScheme B S hS).map_injective
  rw [Functor.map_comp, toScheme_map_siteComb, toScheme_map_siteComb, Category.assoc,
    affineComb_comp (g := (BigFppfOver.toScheme B S hS).map g)
      (hz' := fun k => congrArg (fun p => (BigFppfOver.toScheme B S hS).map g p) (hz k))
      (he' := fun k => by
        simpa only [Category.assoc] using congrArg (· ≫ (BigFppfOver.toScheme B S hS).map g)
          (reduction_comp_eq e e' i hi (hag k)))]
  congr 1

/-- Precomposing with an endomorphism induced by `Spec.map ρ` acts by `Spec.map ρ` on the
presentation. -/
private theorem inv_comp_map_comp_of_map_eq {R' : CommRingCat.{u}}
    (e' : (BigFppfOver.toScheme B S hS).obj T' ≅ Spec R') {Z : BigFppfOver B S hS}
    (ρ : R' ⟶ R') (σ : T' ⟶ T')
    (hσ : (BigFppfOver.toScheme B S hS).map σ = e'.hom ≫ Spec.map ρ ≫ e'.inv) (m : T' ⟶ Z) :
    e'.inv ≫ (BigFppfOver.toScheme B S hS).map (σ ≫ m) =
      Spec.map ρ ≫ e'.inv ≫ (BigFppfOver.toScheme B S hS).map m := by
  rw [Functor.map_comp, hσ]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- **Affine combinations commute with an automorphism of the presentation**, induced by a local
ring map `ρ` of `R` and restricting to `T`, which acts on the coefficients. -/
theorem comp_siteComb_of_specMap {Z : BigFppfOver B S hS} (ℓ : ι → (T' ⟶ Z))
    (z : (BigFppfOver.toScheme B S hS).obj Z)
    (hz : ∀ k, (e'.inv ≫ (BigFppfOver.toScheme B S hS).map (ℓ k)) (closedPoint R) = z)
    (c : ι → R) (hc : ∑ k, c k = 1) (i₀ : ι) (hag : ∀ k, i ≫ ℓ k = i ≫ ℓ i₀) (ρ : R ⟶ R)
    [IsLocalHom ρ.hom] (σ : T' ⟶ T')
    (hσ : (BigFppfOver.toScheme B S hS).map σ = e'.hom ≫ Spec.map ρ ≫ e'.inv)
    (hz' : ∀ k, (e'.inv ≫ (BigFppfOver.toScheme B S hS).map (σ ≫ ℓ k)) (closedPoint R) = z)
    (hc' : ∑ k, ρ (c k) = 1) (hag' : ∀ k, i ≫ σ ≫ ℓ k = i ≫ σ ≫ ℓ i₀) :
    σ ≫ siteComb hJ e e' i hi ℓ z hz c hc i₀ hag =
      siteComb hJ e e' i hi (fun k => σ ≫ ℓ k) z hz' (fun k => ρ (c k)) hc' i₀ hag' := by
  have hσ' := inv_comp_map_comp_of_map_eq e' ρ σ hσ (Z := Z)
  apply (BigFppfOver.toScheme B S hS).map_injective
  rw [Functor.map_comp, toScheme_map_siteComb, toScheme_map_siteComb, hσ]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [specMap_comp_affineComb (hz' := fun k => by rw [← hσ']; exact hz' k) (hc' := hc')
      (he' := fun k => by
        have h := reduction_comp_eq e e' i hi (hag' k)
        rwa [hσ', hσ'] at h)]
  congr 1
  exact affineComb_congr (fun k => (hσ' (ℓ k)).symm) rfl _ _ (fun _ => rfl) _ _ _ _

/-- **Reindexing an affine combination.** -/
theorem siteComb_reindex {Z : BigFppfOver B S hS} (ℓ : ι → (T' ⟶ Z))
    (z : (BigFppfOver.toScheme B S hS).obj Z)
    (hz : ∀ k, (e'.inv ≫ (BigFppfOver.toScheme B S hS).map (ℓ k)) (closedPoint R) = z)
    (c : ι → R) (hc : ∑ k, c k = 1) (i₀ : ι) (hag : ∀ k, i ≫ ℓ k = i ≫ ℓ i₀) (π : ι ≃ ι)
    (hc' : ∑ k, c (π k) = 1) (hag' : ∀ k, i ≫ ℓ (π k) = i ≫ ℓ (π i₀)) :
    siteComb hJ e e' i hi (fun k => ℓ (π k)) z (fun k => hz (π k)) (fun k => c (π k)) hc' i₀
      hag' = siteComb hJ e e' i hi ℓ z hz c hc i₀ hag := by
  apply (BigFppfOver.toScheme B S hS).map_injective
  rw [toScheme_map_siteComb, toScheme_map_siteComb]
  congr 1
  exact affineComb_reindex (fun k => e'.inv ≫ (BigFppfOver.toScheme B S hS).map (ℓ k)) z hz c hc
    i₀ (fun k => reduction_comp_eq e e' i hi (hag k)) π hc'
    (fun k => reduction_comp_eq e e' i hi (hag' k))

/-- Affine combinations of pointwise equal families with pointwise equal coefficients are
equal. -/
theorem siteComb_congr {Z : BigFppfOver B S hS} {ℓ ℓ' : ι → (T' ⟶ Z)} (hℓ : ∀ k, ℓ k = ℓ' k)
    {z z' : (BigFppfOver.toScheme B S hS).obj Z} (hzz : z = z')
    (hz : ∀ k, (e'.inv ≫ (BigFppfOver.toScheme B S hS).map (ℓ k)) (closedPoint R) = z)
    (hz' : ∀ k, (e'.inv ≫ (BigFppfOver.toScheme B S hS).map (ℓ' k)) (closedPoint R) = z')
    {c c' : ι → R} (hcc : ∀ k, c k = c' k) (hc : ∑ k, c k = 1) (hc' : ∑ k, c' k = 1)
    (i₀ : ι) (hag : ∀ k, i ≫ ℓ k = i ≫ ℓ i₀) (hag' : ∀ k, i ≫ ℓ' k = i ≫ ℓ' i₀) :
    siteComb hJ e e' i hi ℓ z hz c hc i₀ hag = siteComb hJ e e' i hi ℓ' z' hz' c' hc' i₀ hag' := by
  obtain rfl : ℓ = ℓ' := funext hℓ
  obtain rfl : c = c' := funext hcc
  subst hzz
  rfl

/-- Postcomposition with `g` sends a family's common image of the closed point to its image
under `g`. -/
private theorem closedPoint_comp_eq_map {Z W : BigFppfOver B S hS} (ℓ : T' ⟶ Z) (g : Z ⟶ W)
    {z : (BigFppfOver.toScheme B S hS).obj Z}
    (hz : (e'.inv ≫ (BigFppfOver.toScheme B S hS).map ℓ) (closedPoint R) = z) :
    (e'.inv ≫ (BigFppfOver.toScheme B S hS).map (ℓ ≫ g)) (closedPoint R) =
      (BigFppfOver.toScheme B S hS).map g z := by
  rw [Functor.map_comp, ← Category.assoc]
  exact congrArg (fun p => (BigFppfOver.toScheme B S hS).map g p) hz

/-- **Affine combinations commute with postcomposition**, in the form: a family `m` whose
postcompositions with `g` are `ℓ` has affine combination composing with `g` to that of `ℓ`. -/
theorem siteComb_comp_of_comp_eq {Z W : BigFppfOver B S hS} (m : ι → (T' ⟶ Z))
    (zm : (BigFppfOver.toScheme B S hS).obj Z)
    (hzm : ∀ k, (e'.inv ≫ (BigFppfOver.toScheme B S hS).map (m k)) (closedPoint R) = zm)
    (c : ι → R) (hc : ∑ k, c k = 1) (i₀ : ι) (hagm : ∀ k, i ≫ m k = i ≫ m i₀) (g : Z ⟶ W)
    {ℓ : ι → (T' ⟶ W)} (hℓ : ∀ k, m k ≫ g = ℓ k) (z : (BigFppfOver.toScheme B S hS).obj W)
    (hz : ∀ k, (e'.inv ≫ (BigFppfOver.toScheme B S hS).map (ℓ k)) (closedPoint R) = z)
    (hag : ∀ k, i ≫ ℓ k = i ≫ ℓ i₀) :
    siteComb hJ e e' i hi m zm hzm c hc i₀ hagm ≫ g = siteComb hJ e e' i hi ℓ z hz c hc i₀ hag := by
  rw [siteComb_comp (hJ := hJ) (hi := hi) m zm hzm c hc i₀ hagm g
      (fun k => closedPoint_comp_eq_map _ g (hzm k))
    fun k => by simp only [← Category.assoc, hagm k]]
  refine siteComb_congr hℓ ?_ _ _ (fun _ => rfl) _ _ _ _ _
  rw [← hz i₀, ← hℓ i₀, ← hzm i₀, Functor.map_comp, ← Category.assoc]
  rfl

/-- An affine combination of a constant family is its member. -/
theorem siteComb_const {Z : BigFppfOver B S hS} (m : T' ⟶ Z)
    (z : (BigFppfOver.toScheme B S hS).obj Z)
    (hz : ∀ _k : ι, (e'.inv ≫ (BigFppfOver.toScheme B S hS).map m) (closedPoint R) = z)
    (c : ι → R) (hc : ∑ k, c k = 1) (i₀ : ι) :
    siteComb hJ e e' i hi (fun _ => m) z hz c hc i₀ (fun _ => rfl) = m := by
  apply (BigFppfOver.toScheme B S hS).map_injective
  rw [toScheme_map_siteComb, affineComb_const (I := J) (hI := hJ)
    (e'.inv ≫ (BigFppfOver.toScheme B S hS).map m) z (hz i₀) c hc i₀]
  simp

section Averaging

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U : BigFppfOver B S hS} (a : yoneda.obj U ⟶ X)

omit [IsLocalRing R] in
private theorem yoneda_map_comp_eq {W : BigFppfOver B S hS} {ℓ ℓ' : W ⟶ U}
    (h : a.app (op W) ℓ = a.app (op W) ℓ') : yoneda.map ℓ ≫ a = yoneda.map ℓ' ≫ a := by
  apply yonedaEquiv.injective
  rwa [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_yoneda_map]

omit [IsLocalRing R] in
private theorem app_eq_of_yoneda_map_comp_eq {W : BigFppfOver B S hS} {ℓ ℓ' : W ⟶ U}
    (h : yoneda.map ℓ ≫ a = yoneda.map ℓ' ≫ a) : a.app (op W) ℓ = a.app (op W) ℓ' := by
  have := congrArg yonedaEquiv h
  rwa [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_yoneda_map] at this

/-- **Two families of solutions through a representable chart with the same images have affine
combinations with the same image.** The two families assemble into a family of morphisms into
the self-fibre product `U ×_X U` of the chart, whose affine combination projects to the two
affine combinations. -/
theorem app_siteComb_eq_of_app_eq (ha : yoneda.relativelyRepresentable a)
    (ℓ ℓ' : ι → (T' ⟶ U)) (z z' : (BigFppfOver.toScheme B S hS).obj U)
    (hz : ∀ k, (e'.inv ≫ (BigFppfOver.toScheme B S hS).map (ℓ k)) (closedPoint R) = z)
    (hz' : ∀ k, (e'.inv ≫ (BigFppfOver.toScheme B S hS).map (ℓ' k)) (closedPoint R) = z')
    (c : ι → R) (hc : ∑ k, c k = 1) (i₀ : ι) (hag : ∀ k, i ≫ ℓ k = i ≫ ℓ i₀)
    (hag' : ∀ k, i ≫ ℓ' k = i ≫ ℓ' i₀) (hX : ∀ k, a.app (op T') (ℓ k) = a.app (op T') (ℓ' k)) :
    a.app (op T') (siteComb hJ e e' i hi ℓ z hz c hc i₀ hag) =
      a.app (op T') (siteComb hJ e e' i hi ℓ' z' hz' c hc i₀ hag') := by
  let m : ι → (T' ⟶ ha.pullback a) := fun k =>
    ha.lift' (ℓ k) (ℓ' k) (yoneda_map_comp_eq a (hX k))
  have hm₁ : ∀ k, m k ≫ ha.fst' a = ℓ k := fun k => ha.lift'_fst _ _ _
  have hm₂ : ∀ k, m k ≫ ha.snd a = ℓ' k := fun k => ha.lift'_snd _ _ _
  have hagm : ∀ k, i ≫ m k = i ≫ m i₀ := fun k => by
    apply ha.hom_ext'
    · simp only [Category.assoc, hm₁, hag k]
    · simp only [Category.assoc, hm₂, hag' k]
  have hzm := apply_closedPoint_eq_of_agree hJ e e' i hi m i₀ hagm
  rw [← siteComb_comp_of_comp_eq (hJ := hJ) (hi := hi) m _ hzm c hc i₀ hagm (ha.fst' a) hm₁ z hz
    hag, ← siteComb_comp_of_comp_eq (hJ := hJ) (hi := hi) m _ hzm c hc i₀ hagm (ha.snd a) hm₂ z'
    hz' hag']
  apply app_eq_of_yoneda_map_comp_eq
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, ha.map_fst', ha.w]

/-- **The averaged lift is invariant.** If a family `Ψ` of morphisms `T' ⟶ U` agreeing on `T`
satisfies `a (s σ ≫ Ψ τ) = a (Ψ (σ * τ))`, then the image in `X` of its affine combination with
coefficients `ρ τ c` is invariant under `s σ`. -/
theorem app_comp_siteComb_average_eq (ha : yoneda.relativelyRepresentable a)
    {G : Type*} [Group G] [Fintype G] (ρ : G →* (R ≃+* R)) (s : G → (T' ⟶ T'))
    (hs : ∀ σ, (BigFppfOver.toScheme B S hS).map (s σ) =
      e'.hom ≫ Spec.map (CommRingCat.ofHom (ρ σ : R →+* R)) ≫ e'.inv)
    (t : G → (T ⟶ T)) (ht : ∀ σ, t σ ≫ i = i ≫ s σ) (c : R) (hc : ∑ σ, ρ σ c = 1)
    (Ψ : G → (T' ⟶ U)) (z : (BigFppfOver.toScheme B S hS).obj U)
    (hz : ∀ τ, (e'.inv ≫ (BigFppfOver.toScheme B S hS).map (Ψ τ)) (closedPoint R) = z)
    (hag : ∀ τ, i ≫ Ψ τ = i ≫ Ψ 1)
    (hΨ : ∀ σ τ, a.app (op T') (s σ ≫ Ψ τ) = a.app (op T') (Ψ (σ * τ))) (σ : G) :
    a.app (op T') (s σ ≫ siteComb hJ e e' i hi Ψ z hz (fun τ => ρ τ c) hc 1 hag) =
      a.app (op T') (siteComb hJ e e' i hi Ψ z hz (fun τ => ρ τ c) hc 1 hag) := by
  have : IsLocalHom (CommRingCat.ofHom (ρ σ : R →+* R)).hom :=
    inferInstanceAs (IsLocalHom (ρ σ : R →+* R))
  have hρc : ∑ τ, (CommRingCat.ofHom (ρ σ : R →+* R)) (ρ τ c) = 1 := by
    change ∑ τ, ρ σ (ρ τ c) = 1
    rw [← map_sum, hc, map_one]
  have hzσ : ∀ τ, (e'.inv ≫ (BigFppfOver.toScheme B S hS).map (s σ ≫ Ψ τ)) (closedPoint R) =
      z := fun τ => by
    rw [inv_comp_map_comp_of_map_eq e' _ _ (hs σ)]
    change (e'.inv ≫ (BigFppfOver.toScheme B S hS).map (Ψ τ))
      ((Spec.map (CommRingCat.ofHom (ρ σ : R →+* R))) (closedPoint R)) = _
    rw [Spec_closedPoint]
    exact hz τ
  rw [comp_siteComb_of_specMap (ρ := CommRingCat.ofHom (ρ σ : R →+* R)) (σ := s σ)
    (hσ := hs σ) (hz' := hzσ) (hc' := hρc)
    (hag' := fun τ => by rw [← Category.assoc, ← ht, Category.assoc, hag τ, ← Category.assoc,
      ht, Category.assoc])]
  have hagσ : ∀ τ, i ≫ Ψ (σ * τ) = i ≫ Ψ (σ * 1) := fun τ => (hag _).trans (hag _).symm
  have hzσ' := apply_closedPoint_eq_of_agree hJ e e' i hi (fun τ => Ψ (σ * τ)) 1 hagσ
  refine (app_siteComb_eq_of_app_eq (hJ := hJ) (hi := hi) a ha (fun τ => s σ ≫ Ψ τ)
    (fun τ => Ψ (σ * τ)) _ _ hzσ hzσ' (fun τ => ρ σ (ρ τ c)) hρc 1 _ hagσ (hΨ σ)).trans ?_
  congr 1
  have hc' : ∑ τ, ρ (Equiv.mulLeft σ τ) c = 1 := by rw [← hρc]; simp [map_mul]
  refine (siteComb_congr (ℓ' := fun τ => Ψ (Equiv.mulLeft σ τ)) (fun _ => rfl) rfl _
    (fun τ => hzσ' τ) (c' := fun τ => ρ (Equiv.mulLeft σ τ) c)
    (fun τ => by simp [map_mul]) _ hc' 1 _ hagσ).trans ?_
  refine (siteComb_congr (fun _ => rfl) ?_ _ (fun τ => hz (Equiv.mulLeft σ τ)) (fun _ => rfl)
    _ hc' 1 _ (fun τ => (hag _).trans (hag _).symm)).trans ?_
  · exact hz (σ * 1)
  exact siteComb_reindex Ψ _ hz (fun τ => ρ τ c) hc 1 hag (Equiv.mulLeft σ) hc' _

include hJ hi in
/-- **A Galois-invariant solution of an infinitesimal lifting problem through an étale chart.**

Let `T ⊆ T'` be presented as the thickening of the spectrum of a local ring `R` defined by an
ideal `J` with `J ^ 2 = 0`, and let a finite group `G` act on `R` by ring automorphisms `ρ σ`,
on `T'` by the morphisms `s σ` they induce and on `T` compatibly by `t σ`, with some `c ∈ R`
satisfying `∑_σ ρ σ c = 1`. Let `a : h_U ⟶ X` be an étale representable chart, `ψ : U ⟶ V` a
morphism of the site with `a ≫ f = h_ψ`, and suppose the `G`-invariant lifting problem `(x, y)`
has a solution `ℓ₀ : T' ⟶ U` through the chart at a chart point `g` of `x`. Then it has a
`G`-invariant solution in `X`. -/
theorem exists_invariant_lift {G : Type*} [Group G] [Fintype G] (ρ : G →* (R ≃+* R))
    (s : G → (T' ⟶ T'))
    (hs : ∀ σ, (BigFppfOver.toScheme B S hS).map (s σ) =
      e'.hom ≫ Spec.map (CommRingCat.ofHom (ρ σ : R →+* R)) ≫ e'.inv)
    (t : G → (T ⟶ T)) (ht : ∀ σ, t σ ≫ i = i ≫ s σ)
    (c : R) (hc : ∑ σ, ρ σ c = 1)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    {V : BigFppfOver B S hS} (f : X ⟶ yoneda.obj V) (ψ : U ⟶ V) (hψ : a ≫ f = yoneda.map ψ)
    (x : X.obj (op T)) (hx : ∀ σ, X.map (t σ).op x = x)
    (y : T' ⟶ V) (hy : ∀ σ, s σ ≫ y = y)
    (g : T ⟶ U) (hg : a.app (op T) g = x)
    (ℓ₀ : T' ⟶ U) (hℓ₀ : i ≫ ℓ₀ = g) (hℓ₀y : ℓ₀ ≫ ψ = y)
    (hiSq : IsSquareZeroClosedImmersion B S hS i) :
    ∃ z : X.obj (op T'), X.map i.op z = x ∧ f.app (op T') z = y ∧
      ∀ σ, X.map (s σ).op z = z := by
  have haE : FormallyEtale a := formallyEtale_of_etale B S hS a ha
  have hnat : ∀ {W W' : BigFppfOver B S hS} (m : W ⟶ W') (ℓ : W' ⟶ U),
      a.app (op W) (m ≫ ℓ) = X.map m.op (a.app (op W') ℓ) := fun m ℓ =>
    NatTrans.naturality_apply a m.op ℓ
  have hfa : ∀ (ℓ : T' ⟶ U), f.app (op T') (a.app (op T') ℓ) = ℓ ≫ ψ := fun ℓ => by
    simpa using congrArg (fun φ => φ.app (op T') ℓ) hψ
  have hss : ∀ σ τ, s σ ≫ s τ = s (σ * τ) := fun σ τ => by
    apply (BigFppfOver.toScheme B S hS).map_injective
    rw [Functor.map_comp, hs, hs, hs, map_mul]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, ← Spec.map_comp_assoc]
    rfl
  have hcond : ∀ σ, a.app (op T) g = X.map i.op (a.app (op T') (s σ ≫ ℓ₀)) := fun σ => by
    rw [← hnat, ← reassoc_of% (ht σ), hnat, hℓ₀, hg, hx]
  have hrel : ∀ τ, ∃ r : T' ⟶ U, i ≫ r = g ∧ a.app (op T') r = a.app (op T') (s τ ≫ ℓ₀) :=
    fun τ => (haE T T' (.of_isIso e.hom) (.of_isIso e'.hom) i hiSq g
      (a.app (op T') (s τ ≫ ℓ₀)) (hcond τ)).exists
  choose Ψ hΨ₀ hΨ using hrel
  have hΨy : ∀ τ, Ψ τ ≫ ψ = y := fun τ => by
    rw [← hfa, hΨ, hfa, Category.assoc, hℓ₀y, hy]
  have hΨa : ∀ σ τ, a.app (op T') (s σ ≫ Ψ τ) = a.app (op T') (Ψ (σ * τ)) := fun σ τ => by
    rw [hnat, hΨ τ, ← hnat, ← Category.assoc, hss, hΨ]
  have hag : ∀ τ, i ≫ Ψ τ = i ≫ Ψ 1 := fun τ => (hΨ₀ τ).trans (hΨ₀ 1).symm
  have hz := apply_closedPoint_eq_of_agree hJ e e' i hi Ψ 1 hag
  let L := siteComb hJ e e' i hi Ψ _ hz (fun τ => ρ τ c) hc 1 hag
  refine ⟨a.app (op T') L, ?_, ?_, fun σ => ?_⟩
  · rw [← hnat, comp_siteComb, hΨ₀, hg]
  · have hz' : ∀ τ, (e'.inv ≫ (BigFppfOver.toScheme B S hS).map (Ψ τ ≫ ψ)) (closedPoint R) =
        (BigFppfOver.toScheme B S hS).map ψ
          ((e'.inv ≫ (BigFppfOver.toScheme B S hS).map (Ψ 1)) (closedPoint R)) :=
      fun τ => closedPoint_comp_eq_map _ ψ (hz τ)
    rw [hfa, siteComb_comp (hz' := hz') (hag' := fun τ => by rw [reassoc_of% (hag τ)]),
      siteComb_congr (ℓ' := fun _ => y) hΨy rfl _
        (fun _ => by rw [← hΨy 1]; exact hz' 1) (fun _ => rfl) hc hc 1 _ (fun _ => rfl)]
    exact siteComb_const y _ _ _ hc 1
  · rw [← hnat]
    exact app_comp_siteComb_average_eq a ha.rep ρ s hs t ht c hc Ψ _ hz hag hΨa σ

end Averaging

end AlgebraicGeometry.Space.GaloisLift

end
