module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.AdditiveSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.RootExtraction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Surjectivity of the Artin–Schreier map on the small étale site

For a scheme `X` of characteristic `p`, the map `x ↦ x ^ p - x` on `𝐆_a` is an epimorphism of
abelian sheaves on the small étale site of `X`, so that

`0 ⟶ ker (F - 1) ⟶ 𝐆_a ⟶ 𝐆_a ⟶ 0`

is a short exact sequence. The content is that the map is locally surjective: every global
function on an étale `X`-scheme is of the form `w ^ p - w` étale-locally.

That is supplied by `Stacks.ArtinSchreier.etale_adjoinRootAS` and its companions: for an element
`a` of a ring `A` of characteristic `p`, the algebra `A[T]/(T ^ p - T - a)` is étale over `A`,
surjective on prime spectra, and contains a root of `T ^ p - T - a`. The passage from that affine
statement to a covering of an arbitrary étale `X`-scheme is by affine open immersions: every
point of a scheme is in the image of an open immersion from an affine scheme, and an open
immersion is étale, so composing gives a jointly surjective family of étale `X`-schemes over
which the given section becomes an Artin–Schreier value.

## Main definitions

* `Stacks.ArtinSchreier.artinSchreierKernelSequence`: the short complex
  `ker (F - 1) ⟶ 𝐆_a ⟶ 𝐆_a`.

## Main results

* `Stacks.ArtinSchreier.exists_etale_surjective_artinSchreier`: the affine step, an étale
  surjective cover of `Spec R` over which a given global function becomes `w ^ p - w`.
* `Stacks.ArtinSchreier.isLocallySurjective_artinSchreierMap`: the Artin–Schreier map is locally
  surjective for the small étale topology.
* `Stacks.ArtinSchreier.epi_artinSchreierMap`: hence an epimorphism of abelian sheaves.
* `Stacks.ArtinSchreier.artinSchreierKernelSequence_shortExact`: **the sequence is short
  exact.**

## Implementation notes

The hypothesis is `(p : Γ(X, ⊤)) = 0`, the literal reading of `X` being of characteristic `p`.
It is used through its images in the rings `R` of the affine open immersions `Spec R ⟶ U.left`,
and nowhere else.

The left term is the kernel of the Artin–Schreier map, not the constant sheaf `𝐙/p𝐙`; the
identification of the two is a separate statement and is not proved here.

## References

* [Stacks Project, Tag 0A3J](https://stacks.math.columbia.edu/tag/0A3J): the Artin–Schreier
  sequence.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

namespace Stacks.ArtinSchreier

/-- **An étale surjective cover of `Spec A` solving an Artin–Schreier equation, at the level of
rings.** For `A` of characteristic `p` and `a` in `A`, the algebra `A[T]/(T ^ p - T - a)` is
étale over `A` and surjective on prime spectra, and `a` becomes of the form `w ^ p - w` in it. -/
theorem exists_etale_artinSchreier (A : CommRingCat.{u}) {p : ℕ} (hp : p.Prime)
    (hA : (p : A) = 0) (a : A) :
    ∃ (S : CommRingCat.{u}) (ϕ : A ⟶ S), Etale (Spec.map ϕ) ∧
      Function.Surjective (Spec.map ϕ).base ∧ ∃ w : S, w ^ p - w = ϕ.hom a := by
  refine ⟨CommRingCat.of (AdjoinRoot (Polynomial.X ^ p - Polynomial.X - Polynomial.C a)),
    CommRingCat.ofHom (algebraMap A _), ?_, comap_surjective_adjoinRootAS a hp.one_lt,
    AdjoinRoot.root _, root_pow_sub_root a⟩
  rw [HasRingHomProperty.Spec_iff (P := @Etale), CommRingCat.hom_ofHom]
  exact RingHom.etale_algebraMap.2 (etale_adjoinRootAS a hp.one_lt hA)

/-- Transporting a solution of an Artin–Schreier equation along `Γ(Spec R, ⊤) ≅ R`: naturality of
that isomorphism turns a solution in `S` into a solution, in the global functions of `Spec S`, of
the equation attached to the global function on `Spec R` corresponding to `a`. -/
theorem artinSchreier_appTop_of_artinSchreier {R S : CommRingCat.{u}} (ϕ : R ⟶ S) {p : ℕ}
    (a : R) (w : S) (hw : w ^ p - w = ϕ.hom a) :
    (Scheme.ΓSpecIso S).inv.hom w ^ p - (Scheme.ΓSpecIso S).inv.hom w =
      (Spec.map ϕ).appTop.hom ((Scheme.ΓSpecIso R).inv.hom a) := by
  rw [← map_pow, ← map_sub, hw]
  exact congrArg (fun (g : R ⟶ Γ(Spec S, ⊤)) => g.hom a) (Scheme.ΓSpecIso_inv_naturality ϕ)

/-- **An étale surjective cover of `Spec R` solving an Artin–Schreier equation for a global
function.** This is `Stacks.ArtinSchreier.exists_etale_artinSchreier` read on global
functions. -/
theorem exists_etale_surjective_artinSchreier (R : CommRingCat.{u}) {p : ℕ} (hp : p.Prime)
    (hR : (p : R) = 0) (y : Γ(Spec R, ⊤)) :
    ∃ (S : CommRingCat.{u}) (ϕ : R ⟶ S), Etale (Spec.map ϕ) ∧
      Function.Surjective (Spec.map ϕ).base ∧ ∃ w : Γ(Spec S, ⊤),
      w ^ p - w = (Spec.map ϕ).appTop.hom y := by
  obtain ⟨a, rfl⟩ : ∃ a : R, (Scheme.ΓSpecIso R).inv.hom a = y :=
    ⟨(Scheme.ΓSpecIso R).hom.hom y, by simp⟩
  obtain ⟨S, ϕ, h1, h2, w, hw⟩ := exists_etale_artinSchreier R hp hR a
  exact ⟨S, ϕ, h1, h2, (Scheme.ΓSpecIso S).inv.hom w,
    artinSchreier_appTop_of_artinSchreier ϕ a w hw⟩

/-- **Étale-local solution of an Artin–Schreier equation, at a point.** Through every point of an
étale `X`-scheme `U` there is an étale morphism `W ⟶ U.left` over which a given global function
on `U` becomes `w ^ p - w`: take an affine open immersion through the point, which is étale, and
compose it with the cover of `Stacks.ArtinSchreier.exists_etale_surjective_artinSchreier`. -/
theorem exists_etale_artinSchreier_of_point (X : Scheme.{u}) {p : ℕ} (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) (U : X.Etale) (x : Γ(U.left, ⊤)) (t : U.left) :
    ∃ (W : Scheme.{u}) (g : W ⟶ U.left) (_ : Etale g) (w : Γ(W, ⊤)),
      t ∈ Set.range g.base ∧ w ^ p - w = g.appTop.hom x := by
  obtain ⟨R, g, hg, y₀, hy₀⟩ := Scheme.exists_Spec_apply_eq t
  have hpR : (p : R) = 0 :=
    (map_natCast ((g ≫ U.hom).appTop ≫ (Scheme.ΓSpecIso R).hom).hom p).symm.trans
      ((congrArg ((g ≫ U.hom).appTop ≫ (Scheme.ΓSpecIso R).hom).hom hX).trans (map_zero _))
  obtain ⟨S, ϕ, hϕ, hsurj, w, hw⟩ :=
    exists_etale_surjective_artinSchreier R hp hpR (g.appTop.hom x)
  refine ⟨Spec S, Spec.map ϕ ≫ g, inferInstance, w, ?_, ?_⟩
  · obtain ⟨z, hz⟩ := hsurj y₀
    exact ⟨z, by rw [show (Spec.map ϕ ≫ g) z = g ((Spec.map ϕ) z) from rfl, hz, hy₀]⟩
  · rw [hw]
    rfl

/-- Pointwise étale solution of Artin–Schreier equations makes the image sieve of a section of
`𝐆_a` covering: the chosen morphisms, viewed in the small étale site, are jointly surjective, and
each of them is in the image sieve because the section becomes an Artin–Schreier value over
it. -/
theorem imageSieve_artinSchreierMap_mem (X : Scheme.{u}) {p : ℕ} (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) (U : X.Etale) (x : Γ(U.left, ⊤))
    (H : ∀ t : U.left, ∃ (W : Scheme.{u}) (g : W ⟶ U.left) (_ : Etale g) (w : Γ(W, ⊤)),
      t ∈ Set.range g.base ∧ w ^ p - w = g.appTop.hom x) :
    Presheaf.imageSieve (artinSchreierMap.{u, v} X hp hX).hom (ofSection.{u, v} x) ∈
      X.smallEtaleTopology U := by
  choose W g hg w ht hw using H
  have hetale (t : U.left) : Etale (g t ≫ U.hom) := by
    have := hg t
    infer_instance
  let Z : U.left → X.Etale := fun t => Scheme.Etale.mk (g t ≫ U.hom)
  let f : (t : U.left) → Z t ⟶ U := fun t => MorphismProperty.Over.homMk (g t) rfl
  have hleft (t : U.left) : (f t).left = g t := rfl
  have hcov : Sieve.ofArrows Z f ∈ X.smallEtaleTopology U := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    exact Set.eq_univ_of_forall fun t => Set.mem_iUnion.2 ⟨t, ht t⟩
  refine X.smallEtaleTopology.superset_covering ?_ hcov
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  rintro V - ⟨t⟩
  refine ⟨ofSection (w t), ?_⟩
  rw [artinSchreierMap_app_ofSection X hp hX (Z t) (w t), map_ofSection (f t) x, hleft t]
  exact congrArg _ (hw t)

/-- **The Artin–Schreier map on `𝐆_a` is locally surjective for the small étale topology**, when
`X` has characteristic `p`. This is exactness on the right, and the only part of it that is not
formal. -/
@[sga "1 XI 6.7" "Right exactness", sga "4 IX 3.5" "partial"]
theorem isLocallySurjective_artinSchreierMap (X : Scheme.{u}) {p : ℕ} (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) :
    Sheaf.IsLocallySurjective (artinSchreierMap.{u, v} X hp hX) := by
  refine ⟨fun {U} s => ?_⟩
  obtain ⟨x, rfl⟩ := ofSection_surjective.{u, v} s
  exact imageSieve_artinSchreierMap_mem X hp hX U x
    (exists_etale_artinSchreier_of_point X hp hX U x)

/-- **The Artin–Schreier map is an epimorphism of abelian sheaves on the small étale site**, when
`X` has characteristic `p`. -/
theorem epi_artinSchreierMap (X : Scheme.{u}) {p : ℕ} (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) : Epi (artinSchreierMap.{u, v} X hp hX) :=
  have := isLocallySurjective_artinSchreierMap.{u, v} X hp hX
  inferInstance

/-- **The Artin–Schreier sequence** `ker (F - 1) ⟶ 𝐆_a ⟶ 𝐆_a` on the small étale site of `X`,
the second map being `x ↦ x ^ p - x` and the first the inclusion of its kernel. -/
def artinSchreierKernelSequence (X : Scheme.{u}) {p : ℕ} (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) :
    ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :=
  ShortComplex.kernelSequence (artinSchreierMap.{u, v} X hp hX)

/-- The first map of the Artin–Schreier sequence, the inclusion of the kernel of the
Artin–Schreier map into `𝐆_a`, is a monomorphism. -/
instance mono_artinSchreierKernelSequence_f (X : Scheme.{u}) {p : ℕ} (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) : Mono (artinSchreierKernelSequence.{u, v} X hp hX).f :=
  inferInstanceAs (Mono (ShortComplex.kernelSequence (artinSchreierMap.{u, v} X hp hX)).f)

/-- **The Artin–Schreier sequence is a short exact sequence of abelian sheaves on the small étale
site of `X`**, for `X` of characteristic `p`.

Exactness on the left and in the middle hold by construction, the left term being the kernel of
the Artin–Schreier map; exactness on the right is
`Stacks.ArtinSchreier.epi_artinSchreierMap`, which rests on the étale solution of
Artin–Schreier equations. -/
@[sga "1 XI 6.7" "Right exactness",
  sga "4 IX 3.5" "partial",
  sga "4½ Fonctions_L 3.1" "surjectivity of Φ − 1"]
theorem artinSchreierKernelSequence_shortExact (X : Scheme.{u}) {p : ℕ} (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) : (artinSchreierKernelSequence.{u, v} X hp hX).ShortExact :=
  .mk' (ShortComplex.kernelSequence_exact _) inferInstance
    (epi_artinSchreierMap.{u, v} X hp hX)

end Stacks.ArtinSchreier

end
