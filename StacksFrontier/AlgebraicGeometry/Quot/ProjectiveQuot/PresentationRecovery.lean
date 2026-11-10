module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.UniversalFlattening
public import StacksFrontier.Topology.Sheaves.Modules.TensorAndDuals.EpiOfConstantRank

/-!
# Recovering the Grassmannian point from the twisted family

Let `K ∈ Quot^P(T)` with quotient `𝒬`, `m = regularityIndex n r P`, and let
`q : 𝒪_T^{⊕ N} ⟶ ℰ` be a Grassmannian presentation (a `T`-point of `G(N - p, N)`). If the twisted
family `ℱ^{(m)}_q = coker(u_m)` is isomorphic to `𝒬(m)` under `𝒪^{⊕ r}(m)`, then `q` is
isomorphic to the presentation `𝒪_T^{⊕ N} ≅ π_*(𝒪^{⊕ r}(m)) ⟶ π_*(𝒬(m))` of `K`: the latter kills
`ker(q)` (its adjoint is `u_m` followed by the quotient map), so it factors through `q` by a
surjection `ℰ ⟶ π_*(𝒬(m))` between finite locally free modules of the same rank `p`, which is an
isomorphism by Stacks 089Q. Consequently a morphism `s : T ⟶ G` with
`(ℙⁿ_s)^* ℱ_G ≅ 𝒬(m)` under `𝒪^{⊕ r}(m)` is the classifying morphism of `K`. In the proof of
Stacks 0DPA this is the step showing that the Grassmannian point of the quotient read off a point
of the flat locus is that point.

## Main results

* `AlgebraicGeometry.ProjectiveQuot.isomorphic_grassmannianPresentation_of_iso`.
* `AlgebraicGeometry.Grassmannian.objEquiv_homEquiv_eq_mk`: the class of `s : T ⟶ G(k, N)` is
  that of `s^* q_G`.
* `AlgebraicGeometry.ProjectiveQuot.eq_toGrassmannian_of_iso`.
* `AlgebraicGeometry.ProjectiveQuot.exists_pullback_universalFamily_iso`: the pullback of `ℱ_G`
  along `toGrassmannian K` is the twisted family of the presentation of `K`.

## References

* [Stacks Project, Tag 0DPA](https://stacks.math.columbia.edu/tag/0DPA)
* [Stacks Project, Tag 089Q](https://stacks.math.columbia.edu/tag/089Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Grassmannian

/-- **The class of `s : T ⟶ G(k, N)` is the class of `s^* q_G`.** -/
theorem objEquiv_homEquiv_eq_mk {k N : ℕ} {T : Scheme.{u}} (s : T ⟶ scheme.{u} k N) :
    (functorData.{u} k N).objEquiv T ((schemeRepresentableBy.{u} k N).homEquiv s) =
      ⟦pullbackPresentation s (universalPresentation k N)⟧ :=
  (Quotient.out_eq _).symm.trans (Quotient.sound (Relation.EqvGen.rel _ _
    (isomorphic_pullbackPresentation_universalPresentation s _ (Quotient.out_eq _).symm)))

end AlgebraicGeometry.Grassmannian

namespace AlgebraicGeometry.ProjectiveQuot

/-- **Factoring through an epimorphism by adjunction**: if the adjoint of `ker f ⟶ X ⟶ R W`
vanishes, `y : X ⟶ R W` factors through the epimorphism `f`. -/
theorem exists_comp_eq_of_homEquiv_symm_eq_zero {C D : Type*} [Category* C] [Abelian C]
    [Category* D] [Abelian D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {X Y : C} {W : D}
    (f : X ⟶ Y) [Epi f] (y : X ⟶ R.obj W) {A : D} (a : L.obj (kernel f) ⟶ A) (b : A ⟶ W)
    (hab : a ≫ b = 0) (h : (adj.homEquiv _ _).symm (kernel.ι f ≫ y) = a ≫ b) :
    ∃ β : Y ⟶ R.obj W, f ≫ β = y := by
  have := adj.isLeftAdjoint
  have hz : kernel.ι f ≫ y = 0 := by
    apply (adj.homEquiv _ _).symm.injective
    rw [h, hab, Adjunction.homEquiv_counit, L.map_zero, zero_comp]
  exact ⟨Abelian.epiDesc f y hz, Abelian.comp_epiDesc f y hz⟩

/-- Bookkeeping in an arbitrary category: `(b ≫ c) ≫ e⁻¹ = b ≫ a` from `a ≫ e = c`. -/
theorem comp_comp_inv_eq_of_eq {C : Type*} [Category* C] {W X Y Y' : C} (b : W ⟶ X) (a : X ⟶ Y)
    (c : X ⟶ Y') (e : Y ≅ Y') (h : a ≫ e.hom = c) : (b ≫ c) ≫ e.inv = b ≫ a := by
  rw [← h, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]

variable {n r : ℕ} {P : Polynomial ℚ}

/-- **A presentation whose twisted family is `𝒬(m)` is the presentation of `K`.** -/
theorem isomorphic_grassmannianPresentation_of_iso
    (hp : quotRank.{u} n r P ≤ freeRank.{u} n r (regularityIndex.{u} n r P))
    {T : Scheme.{u}} {K : Subobject (freeModule n r T)} (hK : K ∈ hilbertFamilies n r P T)
    (q : Grassmannian.QuotientPresentation T
      (freeRank.{u} n r (regularityIndex.{u} n r P) - quotRank.{u} n r P)
      (freeRank.{u} n r (regularityIndex.{u} n r P)))
    (e : presentationCokernel (regularityIndex.{u} n r P) q ≅
      twist (regularityIndex.{u} n r P : ℤ) (quotient K))
    (he : presentationCokernelπ _ q ≫ e.hom =
      twistMap (regularityIndex.{u} n r P : ℤ) (quotientπ K)) :
    q.Isomorphic (grassmannianPresentation hp hK) := by
  let π := projectiveSpaceOver n T ↘ T
  let adj := Scheme.Modules.pullbackPushforwardAdjunction π
  let y := (grassmannianPresentation hp hK).map
  have hy : y = (pushforwardTwistFreeModuleIso (n := n) (r := r) T
        (regularityIndex.{u} n r P)).inv ≫
      (Scheme.Modules.pushforward π).map
        (twistMap (regularityIndex.{u} n r P : ℤ) (quotientπ K)) := rfl
  have h1 : (adj.homEquiv _ _).symm (kernel.ι q.map ≫ y) =
      presentationTwistMap _ q ≫ twistMap (regularityIndex.{u} n r P : ℤ) (quotientπ K) := by
    rw [hy]
    exact (congrArg (adj.homEquiv _ _).symm (Category.assoc _ _ _).symm).trans
      (adj.homEquiv_naturality_right_symm _ _)
  have hc : presentationTwistMap _ q ≫ presentationCokernelπ _ q = 0 :=
    cokernel.condition (presentationTwistMap _ q)
  have h2 : presentationTwistMap _ q ≫
      twistMap (regularityIndex.{u} n r P : ℤ) (quotientπ K) =
        (presentationTwistMap _ q ≫ presentationCokernelπ _ q) ≫ e.hom := by
    rw [← he, Category.assoc]
  obtain ⟨β, hβ⟩ := @exists_comp_eq_of_homEquiv_symm_eq_zero _ _ _ _ _ _ _ _ adj _ _ _ q.map
    q.map_epi y _ (presentationTwistMap _ q ≫ presentationCokernelπ _ q) e.hom
    (by rw [hc, zero_comp]) (h1.trans h2)
  have hepi : Epi β := @epi_of_epi _ _ _ _ _ q.map β
    (hβ ▸ (grassmannianPresentation hp hK).map_epi)
  have hiso : IsIso β :=
    (@Stacks.SheafOfModules.isIso_iff_epi_of_isFiniteLocallyFreeOfRank
      T.toLocallyRingedSpace.toRingedSpace inferInstance inferInstance _ _ _
      q.finiteLocallyFree (grassmannianPresentation hp hK).finiteLocallyFree β).2 hepi
  exact ⟨@asIso _ _ _ _ β hiso, hβ⟩

/-- **A morphism `s : T ⟶ G` whose twisted family is `𝒬(m)` classifies `K`.** -/
theorem eq_toGrassmannian_of_iso
    (hp : quotRank.{u} n r P ≤ freeRank.{u} n r (regularityIndex.{u} n r P))
    {T : Scheme.{u}} {K : Subobject (freeModule n r T)} (hK : K ∈ hilbertFamilies n r P T)
    (s : T ⟶ quotGrassmannian.{u} n r P)
    (e : presentationCokernel (regularityIndex.{u} n r P)
        (Grassmannian.pullbackPresentation s (Grassmannian.universalPresentation _ _)) ≅
      twist (regularityIndex.{u} n r P : ℤ) (quotient K))
    (he : presentationCokernelπ _ _ ≫ e.hom =
      twistMap (regularityIndex.{u} n r P : ℤ) (quotientπ K)) :
    s = toGrassmannian hp hK := by
  apply (Grassmannian.schemeRepresentableBy _ _).homEquiv.injective
  rw [toGrassmannian, Equiv.apply_symm_apply, grassmannianPoint]
  apply ((Grassmannian.functorData _ _).objEquiv T).injective
  rw [Equiv.apply_symm_apply, Grassmannian.objEquiv_homEquiv_eq_mk]
  exact Quotient.sound (Relation.EqvGen.rel _ _
    (isomorphic_grassmannianPresentation_of_iso hp hK _ e he))

/-- **The pullback of `ℱ_G` along `toGrassmannian K` is the twisted family of the presentation
of `K`**, under `𝒪^{⊕ r}(m)`. -/
theorem exists_pullback_universalFamily_iso
    (hp : quotRank.{u} n r P ≤ freeRank.{u} n r (regularityIndex.{u} n r P))
    {T : Scheme.{u}} {K : Subobject (freeModule n r T)} (hK : K ∈ hilbertFamilies n r P T) :
    ∃ e : (Scheme.Modules.pullback (projectiveSpaceOverMap n (toGrassmannian hp hK))).obj
        (universalFamily.{u} n r P) ≅
        presentationCokernel (regularityIndex.{u} n r P) (grassmannianPresentation hp hK),
      (Scheme.Modules.pullback (projectiveSpaceOverMap n (toGrassmannian hp hK))).map
          (presentationCokernelπ _ _) ≫ e.hom =
        (freeTwistPullbackIso n r (toGrassmannian hp hK) _).hom ≫
          presentationCokernelπ _ (grassmannianPresentation hp hK) := by
  obtain ⟨e₁, he₁⟩ := exists_pullback_presentationCokernel_iso (regularityIndex.{u} n r P)
    (toGrassmannian hp hK) (Grassmannian.universalPresentation _ _)
  obtain ⟨e₂, he₂⟩ := exists_presentationCokernel_iso_of_isomorphic
    (regularityIndex.{u} n r P) (grassmannianPresentation_isomorphic_pullback hp hK)
  refine ⟨e₁ ≪≫ e₂.symm, (Category.assoc _ _ _).symm.trans ?_⟩
  exact (congrArg (· ≫ e₂.inv) he₁).trans (comp_comp_inv_eq_of_eq _ _ _ e₂ he₂)

end AlgebraicGeometry.ProjectiveQuot

end
