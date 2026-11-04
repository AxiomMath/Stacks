module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.AffineCoverPreimageVanishing
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.IndEtaleLimitVanishing
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.InjectiveModuleEtaleAcyclic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.Gabber.Theorem
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.CohomologyVanishingTransport
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ClosedFibreProjectiveLineInjective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionInverseImage
public import StacksFrontier.RingTheory.Henselian.Pair.Henselization
import StacksCore.Tactic.StacksAttribute

/-!
# Injective sheaves of modules have no cohomology on closed subschemes above the affine cover size

Stacks 0A51: if `X` has affine diagonal and is covered by `n + 1` affine opens, `Z ⊆ X` is closed,
`𝒜` is a torsion sheaf of rings on `X_étale` and `ℐ` is an injective `𝒜`-module, then
`H^q(Z, ℐ|_Z) = 0` for `q > n`. The induction on `n` is Mayer–Vietoris
(`Stacks.EtaleCohomology.MayerVietoris.subsingleton_H_of_affine_cover`); this file proves the
affine case and assembles the tag.

Let `X` be an affine scheme, `i : Z ⟶ X` a closed immersion and `G` a torsion abelian sheaf on
`X_étale` whose restriction to every affine scheme étale over `X` has no higher cohomology. Then
`H^q(Z, G|_Z) = 0` for every `q > 0`. This is the case `n = 0` of Stacks 0A51, isolated from the
module structure: by Stacks 03F3 and 03FD the underlying abelian sheaf of an injective sheaf of
modules over a torsion sheaf of rings has both properties
(`Stacks.EtaleCohomology.subsingleton_H_etaleAbelianInverseImage_toSheaf_of_injective`,
`Stacks.Torsion.torsionSheafProperty_toSheaf_of_torsion`).

## Proof

Say `X = Spec A` and `Z = Spec (A / I)`. Let `A^h` be the henselization of the pair `(A, I)`
(Stacks 0A02): a filtered colimit of étale `A`-algebras, with `(A^h, IA^h)` henselian and
`A / I = A^h / IA^h`. By Gabber's theorem (Stacks 09ZI) restriction
`H^q(Spec A^h, G|) → H^q(Spec (A^h / IA^h), G|) = H^q(Z, G|_Z)` is bijective, and the source
vanishes by Stacks 09YQ: `Spec A^h` is the limit of the spectra of the étale `A`-algebras
(`Stacks.EtaleCohomology.subsingleton_H_inverseImage_of_indEtale`).

## Main results

* `Stacks.EtaleCohomology.subsingleton_H_quotient_of_torsion_of_etaleAcyclic` — the case
  `X = Spec A`, `Z = Spec (A / I)`.
* `Stacks.EtaleCohomology.subsingleton_H_closed_of_isAffine_of_torsion_of_etaleAcyclic` — the
  case of an affine `X` and a closed immersion `i : Z ⟶ X`.
* `Stacks.EtaleCohomology.subsingleton_H_closed_of_affine_cover_of_torsion_of_etaleAcyclic` — the
  induction on the number of affine opens, by Mayer–Vietoris.
* `Stacks.EtaleCohomology.subsingleton_H_closed_of_injective_of_affine_cover` — **Stacks 0A51**.

## References

* [Stacks Project, Tag 0A51](https://stacks.math.columbia.edu/tag/0A51)
* [Stacks Project, Tag 0A02](https://stacks.math.columbia.edu/tag/0A02)
* [Stacks Project, Tag 09ZI](https://stacks.math.columbia.edu/tag/09ZI)
* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology

/-- **The affine case of Stacks 0A51 for `X = Spec A` and `Z = Spec (A / I)`.** A torsion abelian
sheaf on `(Spec A)_étale` whose restriction to every affine scheme étale over `Spec A` has no
higher cohomology has no higher cohomology on `Spec (A / I)` either. -/
theorem subsingleton_H_quotient_of_torsion_of_etaleAcyclic (A : Type u) [CommRing A]
    (I : Ideal A) (G : Sheaf (Spec (.of A)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (htors : Stacks.Torsion.torsionSheafProperty (Spec (.of A)).smallEtaleTopology G)
    (hG : ∀ (W : Scheme.{u}) [IsAffine W] (j : W ⟶ Spec (.of A)) [Etale j] (q : ℕ), 0 < q →
      Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} j).obj G) q))
    (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0}
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).obj G) q) := by
  let Ah : Type u := henselization A I
  let J : Ideal Ah := I.map (algebraMap A Ah)
  let h : Spec (.of Ah) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A Ah))
  let FA := (etaleAbelianInverseImage.{u, 0} h).obj G
  have hvan : Subsingleton (Sheaf.H.{u + 1} FA q) :=
    subsingleton_H_inverseImage_of_indEtale (ind_henselization A I) G hG q hq
  have hbij := etaleCohomologyRestrictionMap_bijective_of_henselianPair Ah J
    (henselianPair_henselization A I) FA
    (torsionSheafProperty_etaleAbelianInverseImage.{u, 0} h G htors) q
  let φ : A ⧸ I →+* Ah ⧸ J := Ideal.quotientMap J (algebraMap A Ah) Ideal.le_comap_map
  let e : Spec (.of (Ah ⧸ J)) ≅ Spec (.of (A ⧸ I)) :=
    Scheme.Spec.mapIso
      (RingEquiv.ofBijective φ (bijective_quotientMap_henselization A I)).toCommRingCatIso.op
  have hw : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ h =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
    simp only [e, h, Functor.mapIso_hom, Iso.op_hom, Scheme.Spec_map, Quiver.Hom.unop_op,
      ← Spec.map_comp]
    rfl
  exact (subsingleton_H_inverseImage_iff_of_isIso G q _ _ e.hom hw).1
    (Stacks.CohomologyVanishing.subsingleton_ext_of_iso_target
      ((etaleAbelianInverseImageCompIso'.{u, 0} _ h _ rfl).app G).symm q hbij.2.subsingleton)

/-- If `G` has no higher cohomology on affine schemes étale over `X`, neither has its inverse image
along an étale morphism `f : Y ⟶ X` on affine schemes étale over `Y`. -/
theorem subsingleton_H_etaleAbelianInverseImage_of_etale {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : ∀ (W : Scheme.{u}) [IsAffine W] (j : W ⟶ X) [Etale j] (q : ℕ), 0 < q →
      Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} j).obj G) q))
    (W : Scheme.{u}) [IsAffine W] (j : W ⟶ Y) [Etale j] (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} j).obj
      ((etaleAbelianInverseImage.{u, 0} f).obj G)) q) :=
  Stacks.CohomologyVanishing.subsingleton_ext_of_iso_target
    ((etaleAbelianInverseImageCompIso'.{u, 0} j f (j ≫ f) rfl).app G) q (hG W (j ≫ f) q hq)

/-- **The affine case of Stacks 0A51.** Let `X` be affine, `i : Z ⟶ X` a closed immersion and `G`
a torsion abelian sheaf on `X_étale` whose restriction to every affine scheme étale over `X` has
no higher cohomology. Then `H^q(Z, G|_Z) = 0` for every `q > 0`. -/
theorem subsingleton_H_closed_of_isAffine_of_torsion_of_etaleAcyclic {X Z : Scheme.{u}}
    [IsAffine X] (i : Z ⟶ X) [IsClosedImmersion i]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (htors : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology G)
    (hG : ∀ (W : Scheme.{u}) [IsAffine W] (j : W ⟶ X) [Etale j] (q : ℕ), 0 < q →
      Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} j).obj G) q))
    (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} i).obj G) q) := by
  let eX := X.isoSpec
  obtain ⟨I, e, he⟩ :=
    IsClosedImmersion.Spec_iff.mp (inferInstance : IsClosedImmersion (i ≫ eX.hom))
  refine (subsingleton_H_inverseImage_iff_of_isIso G q i
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ eX.inv) e.hom ?_).2 ?_
  · rw [← Category.assoc, ← he, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · exact Stacks.CohomologyVanishing.subsingleton_ext_of_iso_target
      ((etaleAbelianInverseImageCompIso'.{u, 0} _ eX.inv _ rfl).app G).symm q
      (subsingleton_H_quotient_of_torsion_of_etaleAcyclic Γ(X, ⊤) I _
        (torsionSheafProperty_etaleAbelianInverseImage.{u, 0} eX.inv G htors)
        (subsingleton_H_etaleAbelianInverseImage_of_etale eX.inv G hG) q hq)

/-- **The trace of an affine open on a closed subscheme.** Let `i : Z ⟶ X` be a closed immersion,
`V ⊆ X` an affine open and `G` a torsion abelian sheaf on `X_étale` whose restriction to every
affine scheme étale over `X` has no higher cohomology. Then the cohomology of `G|_Z` over
`Z ∩ V`, read on the one-universe model of the small étale site of `Z`, vanishes in positive
degrees. -/
theorem subsingleton_cohomologyPresheaf_preimage_of_torsion_of_etaleAcyclic {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (htors : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology G)
    (hG : ∀ (W : Scheme.{u}) [IsAffine W] (j : W ⟶ X) [Etale j] (q : ℕ), 0 < q →
      Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} j).obj G) q))
    (V : X.Opens) (hV : IsAffineOpen V) (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H'.{u + 1} ((ConstantTransport.toMayerVietoris Z).obj
      ((etaleAbelianInverseImage.{u, 0} i).obj G)) q
      ((MayerVietoris.opensToSite Z).obj (i ⁻¹ᵁ V))) := by
  have : IsAffine V := hV
  let W := i ⁻¹ᵁ V
  let iV : W.toScheme ⟶ V.toScheme := i ∣_ V
  have : IsClosedImmersion iV := IsZariskiLocalAtTarget.restrict ‹_› V
  let GV := (etaleAbelianInverseImage.{u, 0} V.ι).obj G
  have hvan := subsingleton_H_closed_of_isAffine_of_torsion_of_etaleAcyclic iV GV
    (torsionSheafProperty_etaleAbelianInverseImage.{u, 0} V.ι G htors)
    (subsingleton_H_etaleAbelianInverseImage_of_etale V.ι G hG) q hq
  let e : (etaleRestriction.{u, 0} W.ι).obj ((etaleAbelianInverseImage.{u, 0} i).obj G) ≅
      (etaleAbelianInverseImage.{u, 0} iV).obj GV :=
    ((etaleAbelianInverseImageRestrictionIso.{u, 0} W.ι).app _).symm ≪≫
      ((etaleAbelianInverseImageCompIso'.{u, 0} W.ι i (W.ι ≫ i) rfl).app G).symm ≪≫
      (etaleAbelianInverseImageCompIso'.{u, 0} iV V.ι (W.ι ≫ i) (morphismRestrict_ι i V).symm).app G
  exact ConstantTransport.subsingleton_H'_opensToSite_of_subsingleton_H _ _ _ q
    (ConstantTransport.subsingleton_H_toMayerVietoris_of_subsingleton_H _ _ q
      (Stacks.CohomologyVanishing.subsingleton_ext_of_iso_target e.symm q hvan))

/-- **Stacks 0A51 for a torsion abelian sheaf acyclic on affine étale schemes.** Let `X` be a
scheme with affine diagonal which can be covered by `n + 1` affine opens, `i : Z ⟶ X` a closed
immersion and `G` a torsion abelian sheaf on `X_étale` whose restriction to every affine scheme
étale over `X` has no higher cohomology. Then `H^q(Z, G|_Z) = 0` for every `q > n`. -/
theorem subsingleton_H_closed_of_affine_cover_of_torsion_of_etaleAcyclic {X Z : Scheme.{u}}
    [IsAffineHom (pullback.diagonal (terminal.from X))] (n : ℕ)
    (hX : ∃ U : Fin (n + 1) → X.Opens, (∀ k, IsAffineOpen (U k)) ∧ ⨆ k, U k = ⊤)
    (i : Z ⟶ X) [IsClosedImmersion i] (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (htors : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology G)
    (hG : ∀ (W : Scheme.{u}) [IsAffine W] (j : W ⟶ X) [Etale j] (q : ℕ), 0 < q →
      Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} j).obj G) q))
    (q : ℕ) (hq : n < q) :
    Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} i).obj G) q) := by
  obtain ⟨U, hU, hcov⟩ := hX
  exact ConstantTransport.subsingleton_H_of_subsingleton_H_toMayerVietoris _ _ q
    (MayerVietoris.subsingleton_H_of_affine_cover i _
      (subsingleton_cohomologyPresheaf_preimage_of_torsion_of_etaleAcyclic i G htors hG)
      n U hU hcov q hq)

/-- **[Stacks, Tag 0A51].** Let `X` be a scheme with affine diagonal which can be covered by
`n + 1` affine opens, let `i : Z ⟶ X` be a closed immersion, let `𝒜` be a torsion sheaf of rings
on `X_étale` and let `ℐ` be an injective sheaf of `𝒜`-modules on `X_étale`. Then
`H^q_étale(Z, ℐ|_Z) = 0` for every `q > n`.

Affine diagonal is `IsAffineHom (pullback.diagonal (terminal.from X))`, the diagonal of `X` over
`Spec ℤ`. The sheaf `𝒜` is torsion in the sense of Stacks 0DD7: every local section of its
underlying abelian sheaf is locally annihilated by a positive integer. The restriction `ℐ|_Z` is
the étale inverse image along `i` of the underlying abelian sheaf of `ℐ`, and `H^q_étale` is its
étale cohomology `CategoryTheory.Sheaf.H`. -/
@[stacks 0A51 "X with affine diagonal covered by n + 1 affine opens, Z a closed subscheme, 𝒜 a
torsion sheaf of rings on X_et, ℐ an injective 𝒜-module: H^q_et(Z, ℐ|_Z) = 0 for q > n"]
theorem subsingleton_H_closed_of_injective_of_affine_cover {X Z : Scheme.{u}}
    [IsAffineHom (pullback.diagonal (terminal.from X))] (n : ℕ)
    (hX : ∃ U : Fin (n + 1) → X.Opens, (∀ k, IsAffineOpen (U k)) ∧ ⨆ k, U k = ⊤)
    (i : Z ⟶ X) [IsClosedImmersion i] (𝒜 : Sheaf X.smallEtaleTopology RingCat.{u + 1})
    (h𝒜 : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology
      ((sheafCompose X.smallEtaleTopology (forget₂ RingCat AddCommGrpCat)).obj 𝒜))
    (ℐ : SheafOfModules.{u + 1} 𝒜) [Injective ℐ] (q : ℕ) (hq : n < q) :
    Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} i).obj
      ((SheafOfModules.toSheaf 𝒜).obj ℐ)) q) :=
  subsingleton_H_closed_of_affine_cover_of_torsion_of_etaleAcyclic n hX i _
    (Stacks.Torsion.torsionSheafProperty_toSheaf_of_torsion 𝒜 h𝒜 ℐ)
    (fun _ _ j _ => subsingleton_H_etaleAbelianInverseImage_toSheaf_of_injective j 𝒜 ℐ)
    q hq

end Stacks.EtaleCohomology
