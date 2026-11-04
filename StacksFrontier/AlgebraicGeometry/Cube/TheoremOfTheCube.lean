module

public import StacksFrontier.AlgebraicGeometry.Cube.GlueTrivial
public import StacksFrontier.AlgebraicGeometry.Cube.SeesawClosed
public import StacksFrontier.AlgebraicGeometry.Cube.GeometricallyIntegralProduct
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Cube.Openness

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.CubeRelation

/-!
# The theorem of the cube

Let `k` be a field, `X`, `Y` proper geometrically integral `k`-schemes with rational points
`x`, `y`, and `Z` a connected locally Noetherian `k`-scheme with a rational point `z₀`. An
invertible module `L` on `X × Y × Z` whose restrictions to the faces `x × Y × Z`, `X × y × Z`
and `X × Y × z₀` are trivial is trivial. This is the theorem of the cube, [Stacks, Tag
0BF4](https://stacks.math.columbia.edu/tag/0BF4), in the form in which it is used for abelian
varieties.

## Main results

* `AlgebraicGeometry.Cube.nonempty_iso_unit_of_faces`: the theorem of the cube over a field.
* `Stacks.Groupoids.hasTheoremOfTheCube`: the theorem of the cube for the triple self-product of
  an abelian variety, in the form `Stacks.Groupoids.HasTheoremOfTheCube`.
* `Stacks.Groupoids.nonempty_cubeRelation_of_isAbelianVariety`: **Stacks Tag 0BFE**, the cube
  relation for an invertible module on an abelian variety.

## Implementation notes

Write `P = X ×_k Y` and `q : P ×_k Z ⟶ Z` for the second projection. The set `T` of points of
`Z` over an open neighbourhood of which `L` is trivial is open by definition. On an affine open
`V = Spec R` of `Z`, its trace is the set of primes of `R` over which `L` is trivial on the fibre:
one inclusion is restriction, the other is the openness theorem
`AlgebraicGeometry.Cube.exists_basicOpen_isTrivial_of_isTrivial_fiber`, which uses the faces
`x × Y × Z` and `X × y × Z`. That set is closed by the seesaw principle
(`AlgebraicGeometry.Cube.isClosed_setOf_isTrivial_fiber`), so `T` is closed; it contains `z₀`
because the fibre over the prime of `z₀` is the face `X × Y × z₀`, and so `T = Z` since `Z` is
connected. The local trivializations then glue along the section `(x, y, id)`
(`AlgebraicGeometry.Cube.nonempty_iso_unit_of_locally`).

The open subsets of `Z` are handled through open immersions `t : W ⟶ Z`, and `L` is pulled back
along the base change `P ×_k W ⟶ P ×_k Z` of `t`; triviality of such a pullback descends along
any factorization of the base change, which is all the bookkeeping needed.

## References

* [Stacks Project, Tag 0BF4](https://stacks.math.columbia.edu/tag/0BF4)
* [Stacks Project, Tag 0BF3](https://stacks.math.columbia.edu/tag/0BF3)
* [Stacks Project, Tag 0BFE](https://stacks.math.columbia.edu/tag/0BFE)
* D. Mumford, *Abelian varieties*, §6.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Cube

/-- Triviality of a pulled-back module descends along a factorization. -/
theorem nonempty_iso_unit_of_fac {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C)
    (hc : a ≫ b = c) (M : C.Modules)
    (hM : Nonempty ((Scheme.Modules.pullback b).obj M ≅ SheafOfModules.unit _)) :
    Nonempty ((Scheme.Modules.pullback c).obj M ≅ SheafOfModules.unit _) := by
  obtain ⟨e⟩ := hM
  subst hc
  exact ⟨(Scheme.Modules.pullbackComp a b).symm.app M ≪≫ (Scheme.Modules.pullback a).mapIso e ≪≫
    Scheme.Modules.pullbackUnitIso a⟩

section BaseChange

variable {k : Type u} [Field k] {P Z : Scheme.{u}} (π : P ⟶ Spec (.of k)) (h : Z ⟶ Spec (.of k))

/-- The base change `P ×_k W ⟶ P ×_k Z` of a morphism `t : W ⟶ Z` of `k`-schemes. -/
abbrev baseMap {W : Scheme.{u}} (t : W ⟶ Z) (c : W ⟶ Spec (.of k)) (hc : t ≫ h = c) :
    pullback π c ⟶ pullback π h :=
  pullback.map π c π h (𝟙 _) t (𝟙 _) (by simp) (by simp [hc])

/-- The base change of a composite factors through the base change of the second factor. -/
theorem baseMap_comp {W W' : Scheme.{u}} (s : W' ⟶ W) (t : W ⟶ Z) (c : W ⟶ Spec (.of k))
    (hc : t ≫ h = c) (c' : W' ⟶ Spec (.of k)) (hc' : s ≫ c = c') :
    baseMap π c s c' hc' ≫ baseMap π h t c hc =
      baseMap π h (s ≫ t) c' (by rw [Category.assoc, hc, hc']) := by
  apply pullback.hom_ext <;> simp only [baseMap, pullback.map, Category.assoc, pullback.lift_fst,
      pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]

/-- Triviality over `W` descends to `W'` along any `s : W' ⟶ W`. -/
theorem nonempty_iso_unit_baseMap_comp (L : (pullback π h).Modules) {W W' : Scheme.{u}}
    (s : W' ⟶ W) (t : W ⟶ Z) (c : W ⟶ Spec (.of k)) (hc : t ≫ h = c)
    (t' : W' ⟶ Z) (ht' : s ≫ t = t') (c' : W' ⟶ Spec (.of k)) (hc' : t' ≫ h = c')
    (hL : Nonempty ((Scheme.Modules.pullback (baseMap π h t c hc)).obj L ≅
      SheafOfModules.unit _)) :
    Nonempty ((Scheme.Modules.pullback (baseMap π h t' c' hc')).obj L ≅
      SheafOfModules.unit _) := by
  subst ht'
  refine nonempty_iso_unit_of_fac _ _ _ (baseMap_comp π h s t c hc c' ?_) L hL
  rw [← hc', ← hc, Category.assoc]

/-- Triviality over the base change of an open immersion gives triviality over the inverse image
of its range. -/
theorem nonempty_iso_unit_preimage_of_baseMap (L : (pullback π h).Modules) {W : Scheme.{u}}
    (t : W ⟶ Z) [IsOpenImmersion t] (c : W ⟶ Spec (.of k)) (hc : t ≫ h = c)
    (hL : Nonempty ((Scheme.Modules.pullback (baseMap π h t c hc)).obj L ≅
      SheafOfModules.unit _)) :
    Nonempty ((Scheme.Modules.pullback ((pullback.snd π h) ⁻¹ᵁ t.opensRange).ι).obj L ≅
      SheafOfModules.unit _) := by
  let U := (pullback.snd π h) ⁻¹ᵁ t.opensRange
  have hr : Set.range (U.ι ≫ pullback.snd π h) ⊆ Set.range t := by
    rintro _ ⟨p, rfl⟩
    exact p.2
  let j : (U : Scheme.{u}) ⟶ pullback π c :=
    pullback.lift (U.ι ≫ pullback.fst π h) (IsOpenImmersion.lift t (U.ι ≫ pullback.snd π h) hr)
      (by
        rw [← hc, ← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc, Category.assoc,
          pullback.condition])
  refine nonempty_iso_unit_of_fac j (baseMap π h t c hc) U.ι ?_ L hL
  apply pullback.hom_ext
  · simp only [j, baseMap, pullback.map, Category.assoc, pullback.lift_fst, Category.comp_id]
  · simp only [j, baseMap, pullback.map, Category.assoc, pullback.lift_snd,
      pullback.lift_snd_assoc, IsOpenImmersion.lift_fac, Category.comp_id]

/-- The pullback of an invertible module is invertible, in the `Stacks` spelling. -/
theorem isInvertible_pullback_stacks {A B : Scheme.{u}} (a : A ⟶ B) (M : B.Modules)
    (hM : Stacks.SheafOfModules.IsInvertible B.presheaf B.ringCatIsSheaf M) :
    Stacks.SheafOfModules.IsInvertible A.presheaf A.ringCatIsSheaf
      ((Scheme.Modules.pullback a).obj M) := by
  have : AlgebraicGeometry.SheafOfModules.IsInvertible B.presheaf B.ringCatSheaf.property M :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hM
  exact Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ (isInvertible_pullback a M)

/-- Triviality of a pullback along a composite gives triviality of the iterated pullback. -/
theorem nonempty_iso_unit_pullback_pullback {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C)
    (M : C.Modules)
    (hM : Nonempty ((Scheme.Modules.pullback (a ≫ b)).obj M ≅ SheafOfModules.unit _)) :
    Nonempty ((Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback b).obj M) ≅
      SheafOfModules.unit _) :=
  hM.map fun e => (Scheme.Modules.pullbackComp a b).app M ≪≫ e

/-- Triviality of an iterated pullback gives triviality of the pullback along the composite. -/
theorem nonempty_iso_unit_of_pullback_pullback {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C)
    (c : A ⟶ C) (hc : a ≫ b = c) (M : C.Modules)
    (hM : Nonempty ((Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback b).obj M) ≅
      SheafOfModules.unit _)) :
    Nonempty ((Scheme.Modules.pullback c).obj M ≅ SheafOfModules.unit _) := by
  subst hc
  exact hM.map fun e => (Scheme.Modules.pullbackComp a b).symm.app M ≪≫ e

/-- Triviality of the iterated pullback along `a` and `b` follows from triviality of the pullback
along `c`, when `a ≫ b` factors as `a' ≫ c`. -/
private theorem nonempty_iso_unit_pullback_pullback_of_fac {A B C D : Scheme.{u}} (a : A ⟶ B)
    (b : B ⟶ C) (a' : A ⟶ D) (c : D ⟶ C) (hc : a' ≫ c = a ≫ b) (M : C.Modules)
    (hM : Nonempty ((Scheme.Modules.pullback c).obj M ≅ SheafOfModules.unit _)) :
    Nonempty ((Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback b).obj M) ≅
      SheafOfModules.unit _) :=
  nonempty_iso_unit_pullback_pullback _ _ _ (nonempty_iso_unit_of_fac a' c _ hc M hM)

/-- The point of `Spec R` under the spectrum of the residue field at `𝔭` is `𝔭`. -/
theorem SpecMap_residueField_apply {R : Type u} [CommRing R] (𝔭 : PrimeSpectrum R)
    (p : Spec (.of 𝔭.asIdeal.ResidueField)) :
    Spec.map (CommRingCat.ofHom (algebraMap R 𝔭.asIdeal.ResidueField)) p = 𝔭 := by
  rw [Spec.map_apply]
  refine PrimeSpectrum.ext ?_
  have hp : p.asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ p.asIdeal p.isPrime
  show Ideal.comap (algebraMap R 𝔭.asIdeal.ResidueField) p.asIdeal = 𝔭.asIdeal
  rw [hp, ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]

end BaseChange

section Chart

open Openness

/-- The morphism `Spec κ(𝔭) ⟶ Spec R` of the residue field at a prime. -/
abbrev residueSpec {R : Type u} [CommRing R] (𝔭 : PrimeSpectrum R) :
    Spec (.of 𝔭.asIdeal.ResidueField) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R 𝔭.asIdeal.ResidueField))

variable {k : Type u} [Field k] {X Y Z : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (g : Y ⟶ Spec (.of k)) (h : Z ⟶ Spec (.of k))
  (L : (pullback (pullback.fst f g ≫ f) h).Modules)

/-- The set of points of `Z` over a neighbourhood of which `L` is trivial, the neighbourhoods
being given as open immersions. -/
def trivialLocus : Set Z :=
  {z | ∃ (W : Scheme.{u}) (t : W ⟶ Z) (_ : IsOpenImmersion t), z ∈ Set.range t ∧
    Nonempty ((Scheme.Modules.pullback (baseMap (pullback.fst f g ≫ f) h t (t ≫ h) rfl)).obj L ≅
      SheafOfModules.unit _)}

variable {R : Type u} [CommRing R] [Algebra k R] (ψ : Spec (.of R) ⟶ Z) (hψ : ψ ≫ h = φR R)

/-- **Points of the trivial locus have trivial fibres**: if `ψ 𝔭` lies in the trivial locus,
then `L`, pulled back to `Q_R = (X ×_k Y) ×_k Spec R` along `ψ`, is trivial on the fibre over
`𝔭`. -/
theorem nonempty_iso_unit_fiber_of_mem_trivialLocus (𝔭 : PrimeSpectrum R)
    (hz : ψ 𝔭 ∈ trivialLocus f g h L) :
    Nonempty ((Scheme.Modules.pullback (pullback.fst (qR f g R) (residueSpec 𝔭))).obj
      ((Scheme.Modules.pullback (baseMap (pullback.fst f g ≫ f) h ψ _ hψ)).obj L) ≅
      SheafOfModules.unit _) := by
  obtain ⟨W, t, ht, hzt, hLt⟩ := hz
  have hr : Set.range (residueSpec 𝔭 ≫ ψ) ⊆ Set.range t := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Hom.comp_apply, SpecMap_residueField_apply]
    exact hzt
  have hL' := nonempty_iso_unit_baseMap_comp (pullback.fst f g ≫ f) h L
    (IsOpenImmersion.lift t (residueSpec 𝔭 ≫ ψ) hr) t (t ≫ h) rfl (residueSpec 𝔭 ≫ ψ)
    (IsOpenImmersion.lift_fac t (residueSpec 𝔭 ≫ ψ) hr) (residueSpec 𝔭 ≫ ψ ≫ h)
    (by rw [Category.assoc]) hLt
  have e1 : pullback.fst (pullback.fst f g ≫ f) (φR R) ≫ (pullback.fst f g ≫ f) =
      qR f g R ≫ φR R := pullback.condition
  have e2 : pullback.fst (qR f g R) (residueSpec 𝔭) ≫ qR f g R =
      pullback.snd (qR f g R) (residueSpec 𝔭) ≫ residueSpec 𝔭 := pullback.condition
  refine nonempty_iso_unit_pullback_pullback_of_fac _ _
    (pullback.lift (pullback.fst (qR f g R) (residueSpec 𝔭) ≫
      pullback.fst (pullback.fst f g ≫ f) (φR R)) (pullback.snd (qR f g R) (residueSpec 𝔭)) ?_)
    _ ?_ L hL'
  · rw [Category.assoc, e1, ← Category.assoc, e2, hψ, Category.assoc]
  · apply pullback.hom_ext
    · simp only [baseMap, pullback.map, Category.assoc, pullback.lift_fst, Category.comp_id]
    · simp only [baseMap, pullback.map, Category.assoc, pullback.lift_snd,
        pullback.lift_snd_assoc]
      exact (congrArg (· ≫ ψ) e2.symm).trans (Category.assoc _ _ _)

/-- **Trivializations over a basic open of a chart give points of the trivial locus.** If `ψ`
is an open immersion and `L`, pulled back to `Q_R`, is trivial over the inverse image of a basic
open `D(r)` containing `𝔭`, then `ψ 𝔭` lies in the trivial locus. -/
theorem mem_trivialLocus_of_basicOpen [IsOpenImmersion ψ] (𝔭 : PrimeSpectrum R) (r : R)
    (hr : r ∉ 𝔭.asIdeal)
    (hL : Nonempty ((Scheme.Modules.pullback ((qR f g R) ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι).obj
      ((Scheme.Modules.pullback (baseMap (pullback.fst f g ≫ f) h ψ _ hψ)).obj L) ≅
      SheafOfModules.unit _)) :
    ψ 𝔭 ∈ trivialLocus f g h L := by
  let D : (Spec (.of R)).Opens := PrimeSpectrum.basicOpen r
  let t := D.ι ≫ ψ
  have hmem : 𝔭 ∈ D := hr
  refine ⟨D, t, inferInstance, ⟨⟨𝔭, hmem⟩, rfl⟩, ?_⟩
  let b := baseMap (pullback.fst f g ≫ f) (φR R) D.ι (t ≫ h) (by rw [Category.assoc, hψ])
  have hrange : Set.range b ⊆ Set.range ((qR f g R) ⁻¹ᵁ D).ι := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    show (b ≫ qR f g R) p ∈ D
    have hb : b ≫ qR f g R = pullback.snd _ _ ≫ D.ι := by
      simp only [b, baseMap, pullback.map, pullback.lift_snd]
    rw [hb, Scheme.Hom.comp_apply]
    exact (pullback.snd (pullback.fst f g ≫ f) (t ≫ h) p).2
  refine nonempty_iso_unit_of_fac (IsOpenImmersion.lift _ b hrange) _ _ ?_ L
    (nonempty_iso_unit_of_pullback_pullback _ _ _ rfl L hL)
  rw [← Category.assoc, IsOpenImmersion.lift_fac]
  exact baseMap_comp (pullback.fst f g ≫ f) h D.ι ψ (φR R) hψ (t ≫ h) (by rw [Category.assoc, hψ])

/-- The face `X × y × Z` gives the face `X_R ⟶ Q_R` of the chart. -/
theorem nonempty_iso_unit_jX (y : Spec (.of k) ⟶ Y) (hy : y ≫ g = 𝟙 _)
    (σ : pullback f h ⟶ pullback (pullback.fst f g ≫ f) h)
    (hσ₁ : σ ≫ pullback.fst _ _ ≫ pullback.fst f g = pullback.fst f h)
    (hσ₂ : σ ≫ pullback.fst _ _ ≫ pullback.snd f g = pullback.fst f h ≫ f ≫ y)
    (hσ₃ : σ ≫ pullback.snd _ _ = pullback.snd f h)
    (hL : Nonempty ((Scheme.Modules.pullback σ).obj L ≅ SheafOfModules.unit _)) :
    Nonempty ((Scheme.Modules.pullback (jX f g y hy R)).obj
      ((Scheme.Modules.pullback (baseMap (pullback.fst f g ≫ f) h ψ _ hψ)).obj L) ≅
      SheafOfModules.unit _) := by
  refine nonempty_iso_unit_pullback_pullback_of_fac _ _
    (pullback.map f (φR R) f h (𝟙 _) ψ (𝟙 _) (by simp) (by simp [hψ])) σ ?_ L hL
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [jX, baseMap, pullback.map, Category.assoc, pullback.lift_fst,
        Category.comp_id, hσ₁]
    · simp only [jX, baseMap, pullback.map, Category.assoc, pullback.lift_fst,
        pullback.lift_fst_assoc, pullback.lift_snd, Category.comp_id, hσ₂]
  · simp only [jX, baseMap, pullback.map, Category.assoc, pullback.lift_snd,
      pullback.lift_snd_assoc, Category.comp_id, hσ₃]

/-- The face `x × Y × Z` gives the face `Y_R ⟶ Q_R` of the chart. -/
theorem nonempty_iso_unit_jY (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _)
    (σ : pullback g h ⟶ pullback (pullback.fst f g ≫ f) h)
    (hσ₁ : σ ≫ pullback.fst _ _ ≫ pullback.fst f g = pullback.fst g h ≫ g ≫ x)
    (hσ₂ : σ ≫ pullback.fst _ _ ≫ pullback.snd f g = pullback.fst g h)
    (hσ₃ : σ ≫ pullback.snd _ _ = pullback.snd g h)
    (hL : Nonempty ((Scheme.Modules.pullback σ).obj L ≅ SheafOfModules.unit _)) :
    Nonempty ((Scheme.Modules.pullback (jY f g x hx R)).obj
      ((Scheme.Modules.pullback (baseMap (pullback.fst f g ≫ f) h ψ _ hψ)).obj L) ≅
      SheafOfModules.unit _) := by
  refine nonempty_iso_unit_pullback_pullback_of_fac _ _
    (pullback.map g (φR R) g h (𝟙 _) ψ (𝟙 _) (by simp) (by simp [hψ])) σ ?_ L hL
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [jY, baseMap, pullback.map, Category.assoc, pullback.lift_fst,
        pullback.lift_fst_assoc, Category.comp_id, hσ₁]
    · simp only [jY, baseMap, pullback.map, Category.assoc, pullback.lift_fst,
        pullback.lift_snd, Category.comp_id, hσ₂]
  · simp only [jY, baseMap, pullback.map, Category.assoc, pullback.lift_snd,
      pullback.lift_snd_assoc, Category.comp_id, hσ₃]

include hψ in
/-- **The fibre over the prime of a rational point.** If `ψ 𝔭` is the image of a rational point
`z₀` of `Z`, then the fibre of `Q_R` over `𝔭` maps to `P ×_k Z` through the face `P × z₀`. -/
theorem residueSpec_comp_eq [IsOpenImmersion ψ] (z₀ : Spec (.of k) ⟶ Z) (h0 : z₀ ≫ h = 𝟙 _)
    (𝔭 : PrimeSpectrum R) (p₀ : Spec (.of k)) (hp : ψ 𝔭 = z₀ p₀) :
    residueSpec 𝔭 ≫ ψ = residueSpec 𝔭 ≫ φR R ≫ z₀ := by
  have hr : Set.range z₀ ⊆ Set.range ψ := by
    rintro _ ⟨p, rfl⟩
    have hpp : p = p₀ := Subsingleton.elim _ _
    rw [hpp, ← hp]
    exact ⟨𝔭, rfl⟩
  let z₀' := IsOpenImmersion.lift ψ z₀ hr
  have hz₀ : z₀' ≫ ψ = z₀ := IsOpenImmersion.lift_fac ψ z₀ hr
  let φ₀ := Spec.preimage z₀'
  have hφ₀ : Spec.map φ₀ = z₀' := Spec.map_preimage z₀'
  have hsec : CommRingCat.ofHom (algebraMap k R) ≫ φ₀ = 𝟙 _ := by
    apply Spec.map_injective
    have hψ' : Spec.map (CommRingCat.ofHom (algebraMap k R)) = ψ ≫ h := hψ.symm
    rw [Spec.map_comp, hφ₀, Spec.map_id, hψ', ← Category.assoc, hz₀, h0]
  have hker : RingHom.ker φ₀.hom = 𝔭.asIdeal := by
    have h1 : ψ (z₀' p₀) = ψ 𝔭 := by
      rw [← Scheme.Hom.comp_apply, hz₀, hp]
    have h2 : z₀' p₀ = 𝔭 := ψ.isOpenEmbedding.injective h1
    rw [← hφ₀, Spec.map_apply] at h2
    have hp0 : p₀.asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ p₀.asIdeal p₀.isPrime
    have h3 := congrArg PrimeSpectrum.asIdeal h2
    change Ideal.comap φ₀.hom p₀.asIdeal = 𝔭.asIdeal at h3
    rw [hp0, ← RingHom.ker_eq_comap_bot] at h3
    exact h3
  have H : residueSpec 𝔭 = residueSpec 𝔭 ≫ φR R ≫ Spec.map φ₀ := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    refine congrArg Spec.map ?_
    ext a
    show algebraMap R 𝔭.asIdeal.ResidueField a =
      algebraMap R 𝔭.asIdeal.ResidueField (algebraMap k R (φ₀ a))
    rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, Ideal.ker_algebraMap_residueField, ← hker,
      RingHom.mem_ker, map_sub, sub_eq_zero]
    exact (congrArg (fun m => m.hom (φ₀ a)) hsec).symm
  calc residueSpec 𝔭 ≫ ψ = (residueSpec 𝔭 ≫ φR R ≫ Spec.map φ₀) ≫ ψ := congrArg (· ≫ ψ) H
    _ = residueSpec 𝔭 ≫ φR R ≫ z₀ := by rw [hφ₀, Category.assoc, Category.assoc, hz₀]

/-- **The fibre over the prime of a rational point is the face over that point.** -/
theorem nonempty_iso_unit_fiber_of_face [IsOpenImmersion ψ] (z₀ : Spec (.of k) ⟶ Z)
    (h0 : z₀ ≫ h = 𝟙 _) (𝔭 : PrimeSpectrum R) (p₀ : Spec (.of k)) (hp : ψ 𝔭 = z₀ p₀)
    (hZ : Nonempty ((Scheme.Modules.pullback (pullback.lift (𝟙 _) (pullback.fst f g ≫ f ≫ z₀)
      (by simp [h0]) : pullback f g ⟶ pullback (pullback.fst f g ≫ f) h)).obj L ≅
      SheafOfModules.unit _)) :
    Nonempty ((Scheme.Modules.pullback (pullback.fst (qR f g R) (residueSpec 𝔭))).obj
      ((Scheme.Modules.pullback (baseMap (pullback.fst f g ≫ f) h ψ _ hψ)).obj L) ≅
      SheafOfModules.unit _) := by
  have key := residueSpec_comp_eq h ψ hψ z₀ h0 𝔭 p₀ hp
  have e1 : pullback.fst (pullback.fst f g ≫ f) (φR R) ≫ (pullback.fst f g ≫ f) =
      qR f g R ≫ φR R := pullback.condition
  have e2 : pullback.fst (qR f g R) (residueSpec 𝔭) ≫ qR f g R =
      pullback.snd (qR f g R) (residueSpec 𝔭) ≫ residueSpec 𝔭 := pullback.condition
  refine nonempty_iso_unit_pullback_pullback_of_fac _ _
    (pullback.fst (qR f g R) (residueSpec 𝔭) ≫ pullback.fst (pullback.fst f g ≫ f) (φR R))
    _ ?_ L hZ
  apply pullback.hom_ext
  · simp only [baseMap, pullback.map, Category.assoc, pullback.lift_fst, Category.comp_id]
  · simp only [baseMap, pullback.map, Category.assoc, pullback.lift_snd]
    have e1' : pullback.fst (pullback.fst f g ≫ f) (φR R) ≫ pullback.fst f g ≫ f ≫ z₀ =
        qR f g R ≫ φR R ≫ z₀ := by
      rw [← Category.assoc (pullback.fst f g), ← Category.assoc, e1, Category.assoc]
    rw [e1', ← Category.assoc, e2, Category.assoc, ← key, ← Category.assoc, ← e2,
      Category.assoc]

omit [Algebra k R] in
/-- **Affine charts.** Every point of a locally Noetherian `k`-scheme lies in the image of an
open immersion from the spectrum of a Noetherian `k`-algebra, compatibly with the structure
morphisms. -/
theorem exists_chart [IsLocallyNoetherian Z] (z : Z) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsNoetherianRing R) (_ : Algebra k R)
      (ψ : Spec (.of R) ⟶ Z) (_ : IsOpenImmersion ψ) (_ : ψ ≫ h = φR R), z ∈ Set.range ψ := by
  obtain ⟨V, hV, hzV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := z) trivial
  let φ : CommRingCat.of k ⟶ Γ(Z, V) :=
    (Scheme.ΓSpecIso (.of k)).inv ≫ h.appLE ⊤ V le_top
  let : Algebra k Γ(Z, V) := φ.hom.toAlgebra
  have hN : IsNoetherianRing Γ(Z, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  refine ⟨Γ(Z, V), inferInstance, hN, inferInstance, hV.fromSpec, inferInstance, ?_, ?_⟩
  · have e := IsAffineOpen.SpecMap_appLE_fromSpec h (isAffineOpen_top (Spec (.of k))) hV le_top
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at e
    exact e.symm
  · rw [IsAffineOpen.range_fromSpec]
    exact hzV

end Chart

section Faces

variable {k : Type u} [Field k] {X Y Z : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (g : Y ⟶ Spec (.of k)) (h : Z ⟶ Spec (.of k))

/-- The face `X × y × Z ⟶ (X ×_k Y) ×_k Z`, `(x', z) ↦ (x', y, z)`. -/
abbrev productFaceX (y : Spec (.of k) ⟶ Y) (hy : y ≫ g = 𝟙 _) :
    pullback f h ⟶ pullback (pullback.fst f g ≫ f) h :=
  pullback.map f h (pullback.fst f g ≫ f) h (pullback.lift (𝟙 X) (f ≫ y) (by simp [hy]))
    (𝟙 Z) (𝟙 _) (by rw [pullback.lift_fst_assoc, Category.id_comp, Category.comp_id]) (by simp)

/-- The face `x × Y × Z ⟶ (X ×_k Y) ×_k Z`, `(y', z) ↦ (x, y', z)`. -/
abbrev productFaceY (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _) :
    pullback g h ⟶ pullback (pullback.fst f g ≫ f) h :=
  pullback.map g h (pullback.fst f g ≫ f) h (pullback.lift (g ≫ x) (𝟙 Y) (by simp [hx]))
    (𝟙 Z) (𝟙 _)
    (by rw [pullback.lift_fst_assoc, Category.assoc, hx, Category.comp_id])
    (by simp)

/-- The face `X × Y × z₀ ⟶ (X ×_k Y) ×_k Z`, `p ↦ (p, z₀)`. -/
abbrev productFaceZ (z₀ : Spec (.of k) ⟶ Z) (h0 : z₀ ≫ h = 𝟙 _) :
    pullback f g ⟶ pullback (pullback.fst f g ≫ f) h :=
  pullback.lift (𝟙 _) (pullback.fst f g ≫ f ≫ z₀) (by simp [h0])

end Faces

section Main

open Openness

variable {k : Type u} [Field k] {X Y Z : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (g : Y ⟶ Spec (.of k)) (h : Z ⟶ Spec (.of k))

/-- **The theorem of the cube over a field** ([Stacks, Tag 0BF4], the special case used for
abelian varieties). Let `X`, `Y` be proper geometrically integral `k`-schemes with rational
points `x`, `y`, and `Z` a connected locally Noetherian `k`-scheme with a rational point `z₀`. An
invertible module on `(X ×_k Y) ×_k Z` which is trivial on the three faces `X × y × Z`,
`x × Y × Z` and `X × Y × z₀` is trivial. -/
theorem nonempty_iso_unit_of_faces [IsProper f] [GeometricallyIntegral f]
    [IsProper g] [GeometricallyIntegral g] (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _)
    (y : Spec (.of k) ⟶ Y) (hy : y ≫ g = 𝟙 _)
    [ConnectedSpace Z] [IsLocallyNoetherian Z] (z₀ : Spec (.of k) ⟶ Z) (h0 : z₀ ≫ h = 𝟙 _)
    (L : (pullback (pullback.fst f g ≫ f) h).Modules)
    (hL : Stacks.SheafOfModules.IsInvertible (pullback (pullback.fst f g ≫ f) h).presheaf
      (pullback (pullback.fst f g ≫ f) h).ringCatIsSheaf L)
    (hX : Nonempty ((Scheme.Modules.pullback (productFaceX f g h y hy)).obj L ≅
      SheafOfModules.unit _))
    (hY : Nonempty ((Scheme.Modules.pullback (productFaceY f g h x hx)).obj L ≅
      SheafOfModules.unit _))
    (hZ : Nonempty ((Scheme.Modules.pullback (productFaceZ f g h z₀ h0)).obj L ≅
      SheafOfModules.unit _)) :
    Nonempty (L ≅ SheafOfModules.unit _) := by
  let T := trivialLocus f g h L
  have hchart : ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [Algebra k R]
      (ψ : Spec (.of R) ⟶ Z) [IsOpenImmersion ψ] (hψ : ψ ≫ h = φR R) (𝔭 : PrimeSpectrum R),
      ψ 𝔭 ∈ T ↔ Nonempty ((Scheme.Modules.pullback (pullback.fst (qR f g R)
        (residueSpec 𝔭))).obj ((Scheme.Modules.pullback
          (baseMap (pullback.fst f g ≫ f) h ψ _ hψ)).obj L) ≅ SheafOfModules.unit _) := by
    intro R _ _ _ ψ _ hψ 𝔭
    refine ⟨nonempty_iso_unit_fiber_of_mem_trivialLocus f g h L ψ hψ 𝔭, fun hfib => ?_⟩
    have hLR : Stacks.SheafOfModules.IsInvertible
        (pullback (pullback.fst f g ≫ f) (φR R)).presheaf
        (pullback (pullback.fst f g ≫ f) (φR R)).ringCatIsSheaf
        ((Scheme.Modules.pullback (baseMap (pullback.fst f g ≫ f) h ψ _ hψ)).obj L) :=
      isInvertible_pullback_stacks _ L hL
    have hfX := nonempty_iso_unit_jX f g h L ψ hψ y hy (productFaceX f g h y hy)
      (by simp only [productFaceX, pullback.map, Category.assoc, pullback.lift_fst_assoc,
        pullback.lift_fst, Category.comp_id])
      (by simp only [productFaceX, pullback.map, Category.assoc, pullback.lift_fst_assoc,
        pullback.lift_snd, Category.comp_id])
      (by simp only [productFaceX, pullback.map, pullback.lift_snd, Category.comp_id]) hX
    have hfY := nonempty_iso_unit_jY f g h L ψ hψ x hx (productFaceY f g h x hx)
      (by simp only [productFaceY, pullback.map, Category.assoc, pullback.lift_fst_assoc,
        pullback.lift_fst, Category.comp_id])
      (by simp only [productFaceY, pullback.map, Category.assoc, pullback.lift_fst_assoc,
        pullback.lift_snd, Category.comp_id])
      (by simp only [productFaceY, pullback.map, pullback.lift_snd, Category.comp_id]) hY
    obtain ⟨r, hr, hLr⟩ := exists_basicOpen_isTrivial_of_isTrivial_fiber f g x hx y hy _ hLR hfX hfY
      𝔭 hfib
    exact mem_trivialLocus_of_basicOpen f g h L ψ hψ 𝔭 r hr hLr
  have hTo : IsOpen T := by
    rw [isOpen_iff_forall_mem_open]
    rintro z ⟨W, t, ht, hzt, hLt⟩
    exact ⟨Set.range t, fun z' hz' => ⟨W, t, ht, hz', hLt⟩, t.isOpenEmbedding.isOpen_range, hzt⟩
  have hTc : IsClosed T := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro z hz
    obtain ⟨R, _, _, _, ψ, _, hψ, 𝔭, rfl⟩ := exists_chart h z
    let S := {𝔮 : PrimeSpectrum R | Nonempty ((Scheme.Modules.pullback (pullback.fst (qR f g R)
        (residueSpec 𝔮))).obj ((Scheme.Modules.pullback
          (baseMap (pullback.fst f g ≫ f) h ψ _ hψ)).obj L) ≅ SheafOfModules.unit _)}
    have hS : IsClosed S := isClosed_setOf_isTrivial_fiber (pullback.fst f g ≫ f) _
      (isInvertible_pullback_stacks _ L hL)
    refine ⟨ψ '' Sᶜ, ?_, ψ.isOpenEmbedding.isOpenMap _ hS.isOpen_compl, ⟨𝔭, ?_, rfl⟩⟩
    · rintro _ ⟨𝔮, h𝔮, rfl⟩ h𝔮T
      exact h𝔮 ((hchart ψ hψ 𝔮).mp h𝔮T)
    · exact fun h𝔭 => hz ((hchart ψ hψ 𝔭).mpr h𝔭)
  obtain ⟨p₀⟩ : Nonempty (Spec (.of k)) := inferInstance
  have hz₀ : z₀ p₀ ∈ T := by
    obtain ⟨R, _, _, _, ψ, _, hψ, 𝔭, h𝔭⟩ := exists_chart h (z₀ p₀)
    rw [← h𝔭]
    exact (hchart ψ hψ 𝔭).mpr
      (nonempty_iso_unit_fiber_of_face f g h L ψ hψ z₀ h0 𝔭 p₀ h𝔭 hZ)
  have hT : T = Set.univ := IsClopen.eq_univ ⟨hTc, hTo⟩ ⟨_, hz₀⟩
  refine nonempty_iso_unit_of_locally (pullback.fst f g ≫ f) h L
    (pullback.lift (h ≫ pullback.lift x y (by simp [hx, hy])) (𝟙 Z)
      (by rw [Category.assoc, pullback.lift_fst_assoc, hx, Category.comp_id, Category.id_comp]))
    (pullback.lift_snd _ _ _) ?_ fun z => ?_
  · refine nonempty_iso_unit_of_fac (pullback.lift (h ≫ x) (𝟙 Z) (by simp [hx]))
      (productFaceX f g h y hy) _ ?_ L hX
    apply pullback.hom_ext
    · apply pullback.hom_ext <;>
        simp only [productFaceX, pullback.map, Category.assoc, pullback.lift_fst_assoc,
          pullback.lift_fst, pullback.lift_snd, Category.comp_id, reassoc_of% hx]
    · simp only [productFaceX, pullback.map, Category.assoc, pullback.lift_snd, Category.comp_id]
  · have hz : z ∈ T := hT ▸ Set.mem_univ z
    obtain ⟨W, t, ht, hzt, hLt⟩ := hz
    exact ⟨t.opensRange, hzt, nonempty_iso_unit_preimage_of_baseMap _ h L t _ rfl hLt⟩

end Main

end AlgebraicGeometry.Cube

open AlgebraicGeometry AlgebraicGeometry.Cube AlgebraicGeometry.Cube.Openness
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Stacks.Groupoids

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

/-- The identity section of `A` as a rational point of `A`. -/
abbrev unitPoint : Spec (.of k) ⟶ A.left := η[A].left

/-- The identity section `unitPoint A` is a section of the structure morphism of `A`. -/
theorem unitPoint_hom : unitPoint A ≫ A.hom = 𝟙 _ := Over.w η[A]

/-- The underlying morphism of schemes of the constant map `1 : B ⟶ A` is the structure
morphism of `B` followed by `unitPoint A`. -/
theorem one_left {B : Over (Spec (.of k))} : (1 : B ⟶ A).left = B.hom ≫ unitPoint A := rfl

private theorem pullback_lift_hom_eq {A : Over (Spec (.of k))} {T : Scheme.{u}}
    (a b : T ⟶ pullback (pullback.fst A.hom A.hom ≫ A.hom) A.hom)
    (h₁ : a ≫ pullback.fst _ _ ≫ pullback.fst _ _ = b ≫ pullback.fst _ _ ≫ pullback.fst _ _)
    (h₂ : a ≫ pullback.fst _ _ ≫ pullback.snd _ _ = b ≫ pullback.fst _ _ ≫ pullback.snd _ _)
    (h₃ : a ≫ pullback.snd _ _ = b ≫ pullback.snd _ _) : a = b :=
  pullback.hom_ext (pullback.hom_ext (by simpa using h₁) (by simpa using h₂)) h₃

/-- The underlying morphism of the face `cubeFace₂ A`, `(x₁, x₃) ↦ (x₁, e, x₃)`, is
`productFaceX` at the identity section. -/
theorem cubeFace₂_left :
    (cubeFace₂ A).left = productFaceX A.hom A.hom A.hom (unitPoint A) (unitPoint_hom A) := by
  have e : (cubeFace₂ A).left = pullback.lift (f := pullback.fst A.hom A.hom ≫ A.hom) (g := A.hom)
      (pullback.lift (pullback.fst A.hom A.hom) (pullback.fst A.hom A.hom ≫ A.hom ≫ unitPoint A)
        (by simp [pullback.condition]))
      (pullback.snd A.hom A.hom)
      (by rw [pullback.lift_fst_assoc, pullback.condition]) := rfl
  rw [e]
  apply pullback_lift_hom_eq <;>
    simp only [productFaceX, pullback.map, Category.assoc, pullback.lift_fst_assoc,
      pullback.lift_fst, pullback.lift_snd, Category.comp_id]

/-- The underlying morphism of the face `cubeFace₁ A`, `(x₂, x₃) ↦ (e, x₂, x₃)`, is
`productFaceY` at the identity section. -/
theorem cubeFace₁_left :
    (cubeFace₁ A).left = productFaceY A.hom A.hom A.hom (unitPoint A) (unitPoint_hom A) := by
  have e : (cubeFace₁ A).left = pullback.lift (f := pullback.fst A.hom A.hom ≫ A.hom) (g := A.hom)
      (pullback.lift (pullback.fst A.hom A.hom ≫ A.hom ≫ unitPoint A) (pullback.fst A.hom A.hom)
        (by simp))
      (pullback.snd A.hom A.hom)
      (by rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, unitPoint_hom,
        Category.comp_id, pullback.condition]) := rfl
  rw [e]
  apply pullback_lift_hom_eq <;>
    simp only [productFaceY, pullback.map, Category.assoc, pullback.lift_fst_assoc,
      pullback.lift_fst, pullback.lift_snd, Category.comp_id]

/-- The underlying morphism of the face `cubeFace₃ A`, `(x₁, x₂) ↦ (x₁, x₂, e)`, is
`productFaceZ` at the identity section. -/
theorem cubeFace₃_left :
    (cubeFace₃ A).left = productFaceZ A.hom A.hom A.hom (unitPoint A) (unitPoint_hom A) := by
  have e : (cubeFace₃ A).left = pullback.lift (f := pullback.fst A.hom A.hom ≫ A.hom) (g := A.hom)
      (pullback.lift (pullback.fst A.hom A.hom) (pullback.snd A.hom A.hom) pullback.condition)
      (pullback.fst A.hom A.hom ≫ A.hom ≫ unitPoint A) (by simp) := rfl
  rw [e]
  apply pullback_lift_hom_eq <;>
    simp only [productFaceZ, pullback.lift_fst_assoc, pullback.lift_fst, pullback.lift_snd,
      Category.id_comp]

/-- **The theorem of the cube for an abelian variety** ([Stacks, Tag 0BF4], applied to
`X = Y = Z = A` and `x = y = z = e`): an invertible module on `A × A × A` whose pullbacks along
the three faces `e × A × A`, `A × e × A` and `A × A × e` are trivial is trivial. -/
theorem hasTheoremOfTheCube (k : Type u) [Field k] (A : Over (Spec (.of k))) [GrpObj A]
    [IsAbelianVariety k A] :
    HasTheoremOfTheCube A := by
  intro N hN h₁ h₂ h₃
  have : IsProper A.hom := inferInstance
  have : GeometricallyIntegral A.hom := inferInstance
  have : ConnectedSpace A.left := inferInstance
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  obtain ⟨i₁⟩ := h₁
  obtain ⟨i₂⟩ := h₂
  obtain ⟨i₃⟩ := h₃
  obtain ⟨e⟩ := nonempty_iso_unit_of_faces A.hom A.hom A.hom (unitPoint A)
    (unitPoint_hom A) (unitPoint A) (unitPoint_hom A) (unitPoint A) (unitPoint_hom A) N hN
    ⟨(Scheme.Modules.pullbackCongr (cubeFace₂_left A).symm).app N ≪≫ i₂⟩
    ⟨(Scheme.Modules.pullbackCongr (cubeFace₁_left A).symm).app N ≪≫ i₁⟩
    ⟨(Scheme.Modules.pullbackCongr (cubeFace₃_left A).symm).app N ≪≫ i₃⟩
  exact ⟨e⟩

/-- **Stacks Project, Tag 0BFE.** Let `k` be a field, let `A` be an abelian variety over `k`
and let `L` be an invertible `𝒪_A`-module. Then

`m₁₂₃^*L ⊗ m₁^*L ⊗ m₂^*L ⊗ m₃^*L ≅ m₁₂^*L ⊗ m₁₃^*L ⊗ m₂₃^*L`

as invertible modules on `A × A × A`, where `m_I` is the sum of the coordinates indexed by
`I`, written as the product of the corresponding coordinates in the group `A × A × A ⟶ A`. The
theorem of the cube is `Stacks.Groupoids.hasTheoremOfTheCube`. -/
@[stacks 0BFE]
theorem nonempty_cubeRelation_of_isAbelianVariety [IsAbelianVariety k A]
    (L : SheafOfModules.{u} (structureSheafRing A.left.toRingedSpace))
    (hL : Stacks.SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatIsSheaf L) :
    Nonempty
      (Stacks.SheafOfModules.schemeTensor (cubeObj A).left
          (Stacks.SheafOfModules.schemeTensor (cubeObj A).left
            (Stacks.SheafOfModules.schemeTensor (cubeObj A).left
              (pullbackOver (cubeProj₁ A * cubeProj₂ A * cubeProj₃ A) L)
              (pullbackOver (cubeProj₁ A) L))
            (pullbackOver (cubeProj₂ A) L))
          (pullbackOver (cubeProj₃ A) L) ≅
        Stacks.SheafOfModules.schemeTensor (cubeObj A).left
          (Stacks.SheafOfModules.schemeTensor (cubeObj A).left
            (pullbackOver (cubeProj₁ A * cubeProj₂ A) L)
            (pullbackOver (cubeProj₁ A * cubeProj₃ A) L))
          (pullbackOver (cubeProj₂ A * cubeProj₃ A) L)) :=
  nonempty_cubeRelation A (hasTheoremOfTheCube k A) L hL

end Stacks.Groupoids

