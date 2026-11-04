module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.MultiplicativeSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.RootExtraction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Kummer sequence on the small étale site

For a scheme `X` on which `n` is invertible, the sequence

`0 ⟶ μ_n ⟶ 𝐆_m ⟶ 𝐆_m ⟶ 0`,

with the second map the `n`-th power map, is a short exact sequence of abelian sheaves on the
small étale site of `X`. Here `μ_n` is the kernel of the `n`-th power map, `n` is invertible
means `IsUnit ((n : ℕ) : Γ(X, ⊤))`, and `n ≠ 0` is assumed as well. The `n`-th power map is
locally surjective: every invertible global function on an étale `X`-scheme acquires an `n`-th
root étale-locally.

## Main definitions

* `Stacks.Kummer.kummerSequence`: the short complex `μ_n ⟶ 𝐆_m ⟶ 𝐆_m`.

## Main results

* `Stacks.Kummer.exists_etale_surjective_pow`: an étale surjective cover of `Spec R` over which a
  given invertible global function becomes an `n`-th power.
* `Stacks.Kummer.isLocallySurjective_powMap`: the `n`-th power map on `𝐆_m` is locally
  surjective for the small étale topology.
* `Stacks.Kummer.epi_powMap`: the `n`-th power map on `𝐆_m` is an epimorphism of abelian sheaves.
* `Stacks.Kummer.kummerSequence_shortExact`: the Kummer sequence is short exact.

## References

* [Stacks Project, Tag 03PL](https://stacks.math.columbia.edu/tag/03PL): the Kummer sequence.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Polynomial

universe u v

namespace Stacks.Kummer

section Affine

variable {A : Type u} [CommRing A] {n : ℕ}

/-- The `n`-th root of a unit `v` adjoined by `A[T]/(Tⁿ - v)`, as a unit of that ring. -/
def rootUnit (hn : n ≠ 0) (v : Aˣ) : (AdjoinRoot (X ^ n - C (v : A)))ˣ :=
  (isUnit_root_unit hn v).unit

/-- The adjoined root is an `n`-th root of `v` in the unit group. -/
theorem rootUnit_pow (hn : n ≠ 0) (v : Aˣ) :
    rootUnit hn v ^ n =
      Units.map (algebraMap A (AdjoinRoot (X ^ n - C (v : A)))).toMonoidHom v :=
  Units.ext <| (Units.val_pow_eq_pow_val _ _).trans (root_pow_eq_unit v)

end Affine

/-- For `n ≠ 0` invertible in `A` and `v` a unit of `A`, there is a ring map `ϕ : A ⟶ S` with
`Spec.map ϕ` étale and surjective over which `v` becomes an `n`-th power. -/
theorem exists_etale_pow (A : CommRingCat.{u}) {n : ℕ} (hn0 : n ≠ 0)
    (hn : IsUnit ((n : ℕ) : A)) (v : Aˣ) :
    ∃ (S : CommRingCat.{u}) (ϕ : A ⟶ S), Etale (Spec.map ϕ) ∧
      Function.Surjective (Spec.map ϕ).base ∧
      ∃ w : Sˣ, w ^ n = Units.map ϕ.hom.toMonoidHom v := by
  refine ⟨CommRingCat.of (AdjoinRoot (X ^ n - C (v : A))), CommRingCat.ofHom (algebraMap A _), ?_,
    comap_surjective_adjoinRoot_unit hn0 v, rootUnit hn0 v, rootUnit_pow hn0 v⟩
  rw [HasRingHomProperty.Spec_iff (P := @Etale), CommRingCat.hom_ofHom]
  exact RingHom.etale_algebraMap.2 (etale_adjoinRoot_unit hn hn0 v)

/-- An `n`-th root `w` in `S` of the image of a unit `v` of `R` gives, through
`Γ(Spec S, ⊤) ≅ S`, an `n`-th root of the pullback along `Spec.map ϕ` of the global function on
`Spec R` corresponding to `v`. -/
theorem pow_map_appTop_of_pow {R S : CommRingCat.{u}} (ϕ : R ⟶ S) {n : ℕ} (v : Rˣ)
    (w : Sˣ) (hw : w ^ n = Units.map ϕ.hom.toMonoidHom v) :
    (Units.map (Scheme.ΓSpecIso S).inv.hom.toMonoidHom w) ^ n =
      Units.map (Spec.map ϕ).appTop.hom.toMonoidHom
        (Units.map (Scheme.ΓSpecIso R).inv.hom.toMonoidHom v) := by
  rw [← map_pow, hw]
  exact Units.ext (congrArg (fun (g : R ⟶ Γ(Spec S, ⊤)) ↦ g.hom (v : R))
    (Scheme.ΓSpecIso_inv_naturality ϕ))

/-- For `n ≠ 0` invertible in `R`, every invertible global function on `Spec R` becomes an
`n`-th power over some étale surjective morphism `Spec.map ϕ : Spec S ⟶ Spec R`. -/
theorem exists_etale_surjective_pow (R : CommRingCat.{u}) {n : ℕ} (hn0 : n ≠ 0)
    (hn : IsUnit ((n : ℕ) : R)) (y : (Γ(Spec R, ⊤))ˣ) :
    ∃ (S : CommRingCat.{u}) (ϕ : R ⟶ S), Etale (Spec.map ϕ) ∧
      Function.Surjective (Spec.map ϕ).base ∧ ∃ w : (Γ(Spec S, ⊤))ˣ,
      w ^ n = Units.map (Spec.map ϕ).appTop.hom.toMonoidHom y := by
  obtain ⟨v, rfl⟩ : ∃ v : Rˣ, Units.map (Scheme.ΓSpecIso R).inv.hom.toMonoidHom v = y :=
    ⟨Units.map (Scheme.ΓSpecIso R).hom.hom.toMonoidHom y, by apply Units.ext; simp⟩
  obtain ⟨S, ϕ, h1, h2, w, hw⟩ := exists_etale_pow R hn0 hn v
  exact ⟨S, ϕ, h1, h2, Units.map (Scheme.ΓSpecIso S).inv.hom.toMonoidHom w,
    pow_map_appTop_of_pow ϕ v w hw⟩

/-- Through every point of an étale `X`-scheme `U` there is an étale morphism `W ⟶ U.left` over
which a given invertible global function on `U` becomes an `n`-th power. -/
theorem exists_etale_pow_of_point (X : Scheme.{u}) {n : ℕ} (hn0 : n ≠ 0)
    (hX : IsUnit ((n : ℕ) : Γ(X, ⊤))) (U : X.Etale) (x : (Γ(U.left, ⊤))ˣ) (p : U.left) :
    ∃ (W : Scheme.{u}) (q : W ⟶ U.left) (_ : Etale q) (w : (Γ(W, ⊤))ˣ),
      p ∈ Set.range q.base ∧ w ^ n = Units.map q.appTop.hom.toMonoidHom x := by
  obtain ⟨R, g, hg, y₀, hy₀⟩ := Scheme.exists_Spec_apply_eq p
  have hnR : IsUnit ((n : ℕ) : R) := by
    simpa using hX.map ((g ≫ U.hom).appTop ≫ (Scheme.ΓSpecIso R).hom).hom
  obtain ⟨S, ϕ, hϕ, hsurj, w, hw⟩ := exists_etale_surjective_pow R hn0 hnR
    (Units.map g.appTop.hom.toMonoidHom x)
  refine ⟨Spec S, Spec.map ϕ ≫ g, inferInstance, w, ?_, ?_⟩
  · obtain ⟨z, hz⟩ := hsurj y₀
    refine ⟨z, ?_⟩
    have hcomp : (Spec.map ϕ ≫ g) z = g ((Spec.map ϕ) z) := rfl
    rw [hcomp, hz, hy₀]
  · exact hw.trans (Units.ext rfl)

/-- If through every point of `U` there is an étale morphism over which `x` becomes an `n`-th
power, then the image sieve of the section `ofUnit x` of `𝐆_m` under the `n`-th power map is a
covering sieve of `U`. -/
theorem imageSieve_powMap_mem (X : Scheme.{u}) (n : ℕ) (U : X.Etale) (x : (Γ(U.left, ⊤))ˣ)
    (H : ∀ p : U.left, ∃ (W : Scheme.{u}) (q : W ⟶ U.left) (_ : Etale q) (w : (Γ(W, ⊤))ˣ),
      p ∈ Set.range q.base ∧ w ^ n = Units.map q.appTop.hom.toMonoidHom x) :
    Presheaf.imageSieve (powMap.{u, v} X n).hom (ofUnit.{u, v} x) ∈ X.smallEtaleTopology U := by
  choose W q hq w hp hw using H
  have hetale (p : U.left) : Etale (q p ≫ U.hom) := inferInstance
  let Z : U.left → X.Etale := fun p ↦ Scheme.Etale.mk (q p ≫ U.hom)
  let f : (p : U.left) → Z p ⟶ U := fun p ↦ MorphismProperty.Over.homMk (q p) rfl
  have hleft (p : U.left) : (f p).left = q p := rfl
  have hcov : Sieve.ofArrows Z f ∈ X.smallEtaleTopology U := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    exact Set.eq_univ_of_forall fun p ↦ Set.mem_iUnion.2 ⟨p, hp p⟩
  refine X.smallEtaleTopology.superset_covering ?_ hcov
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  rintro V - ⟨p⟩
  refine ⟨ofUnit (w p), ?_⟩
  rw [powMap_app_ofUnit X n (Z p) (w p), map_ofUnit (f p) x, hleft p]
  exact congrArg _ (hw p)

/-- The `n`-th power map on `𝐆_m` is locally surjective for the small étale topology, when `n`
is an invertible global function on `X`. -/
@[sga "4 IX 3.2" "surjectivity clause", sga "4½ Arcata 2.2.5"]
theorem isLocallySurjective_powMap (X : Scheme.{u}) {n : ℕ} (hn0 : n ≠ 0)
    (hX : IsUnit ((n : ℕ) : Γ(X, ⊤))) :
    Sheaf.IsLocallySurjective (powMap.{u, v} X n) := by
  refine ⟨fun {U} s ↦ ?_⟩
  obtain ⟨x, rfl⟩ := ofUnit_surjective.{u, v} s
  exact imageSieve_powMap_mem X n U x (exists_etale_pow_of_point X hn0 hX U x)

/-- The `n`-th power map on `𝐆_m` is an epimorphism of abelian sheaves on the small étale site,
when `n` is an invertible global function on `X`. -/
theorem epi_powMap (X : Scheme.{u}) {n : ℕ} (hn0 : n ≠ 0)
    (hX : IsUnit ((n : ℕ) : Γ(X, ⊤))) : Epi (powMap.{u, v} X n) :=
  have := isLocallySurjective_powMap.{u, v} X hn0 hX
  inferInstance

/-- The Kummer sequence `μ_n ⟶ 𝐆_m ⟶ 𝐆_m` on the small étale site of `X`, the second map
being the `n`-th power map and the first the inclusion of its kernel. -/
@[sga "7 IX 14.3" "partial"]
def kummerSequence (X : Scheme.{u}) (n : ℕ) :
    ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :=
  ShortComplex.kernelSequence (powMap.{u, v} X n)

/-- The first map of the Kummer sequence is a monomorphism. -/
instance mono_kummerSequence_f (X : Scheme.{u}) (n : ℕ) : Mono (kummerSequence.{u, v} X n).f :=
  inferInstanceAs (Mono (ShortComplex.kernelSequence (powMap.{u, v} X n)).f)

/-- The first term of the Kummer sequence is the sheaf `μ_n` of `n`-th roots of unity. -/
@[simp]
theorem kummerSequence_X₁ (X : Scheme.{u}) (n : ℕ) :
    (kummerSequence.{u, v} X n).X₁ = rootsOfUnitySheaf.{u, v} X n :=
  rfl

/-- The Kummer sequence is a short exact sequence of abelian sheaves on the small étale site of
`X`, for `n` an invertible global function on `X`. -/
@[sga "4½ Arcata 2.2.5", sga "4½ Sommes_trig 4.7" "special case", sga "7 IX 14.3" "special case"]
theorem kummerSequence_shortExact (X : Scheme.{u}) {n : ℕ} (hn0 : n ≠ 0)
    (hX : IsUnit ((n : ℕ) : Γ(X, ⊤))) : (kummerSequence.{u, v} X n).ShortExact :=
  .mk' (ShortComplex.kernelSequence_exact _) inferInstance (epi_powMap.{u, v} X hn0 hX)

end Stacks.Kummer

end
