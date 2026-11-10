module

public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.EvenDegreeClopenDecomposition
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.PicardFirstChernClass
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.CupFirstChernClassVanishing
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.SmoothDivisor
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeRegular
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.SubbundleDivisor
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.QCQSScheme

/-!
# Condition (5) of Section 45.12 for even-degree de Rham cohomology

Let `0 ⟶ ℒ ⟶ ℰ ⟶ 𝓕 ⟶ 0` be a short exact sequence of finite locally free modules on a scheme `X`
over `B`, with `ℒ` invertible, and let `i : 𝐏(𝓕) ⟶ 𝐏(ℰ)` be the induced closed immersion. It is
an effective Cartier divisor, the zero scheme of a section of an invertible module
`𝒪_P(𝐏(𝓕))` (`Stacks.WeilCohomology.IsSubbundleDivisorModule`), and both `𝐏(ℰ)` and `𝐏(𝓕)` are
smooth over `X`. So the de Rham complex of log poles is defined for `𝐏(𝓕) ⊆ 𝐏(ℰ)` over `B`
(Lemma 0FMY), and Lemma 0FMX gives condition (5) of Weil Cohomology Theories, Section 45.12 for
`A(X) = ⨁_n H^{2n}_{dR}(X/B)`, as the proof of Lemma 0FW9 says:

if `a ∈ A(𝐏(ℰ))` and `i^*a = 0`, then `a · c₁^{dR}(𝒪_P(𝐏(𝓕))) = 0`.

## Main results

* `Stacks.DeRhamBaseChange.deRhamFirstChernClassPicard_picardClassOf`: on the class of an
  invertible module, `c₁^{dR}` is its de Rham first Chern class.
* `AlgebraicGeometry.SheafOfModules.evenDeRham_mul_of_eq_zero`: products with a class of
  `H^2_{dR}` vanish componentwise.
* `Stacks.DeRhamClopen.evenDeRham_mul_zeroScheme_eq_zero`: Lemma 0FMX on the even-degree ring,
  for the zero scheme of a regular section.
* `Stacks.DeRhamClopen.evenDeRham_mul_subbundleDivisor_eq_zero`: condition (5).
* `Stacks.WeilCohomology.QCQSScheme.exists_isBundleEmbedding_deRhamDivisor`: clause (3)(c) and
  condition (5) for quasi-compact and quasi-separated schemes over `B`, in the shape of
  `Stacks.WeilCohomology.DivisorDatumClause`.

## References

* [Stacks Project, Tag 0FW9](https://stacks.math.columbia.edu/tag/0FW9)
* [Stacks Project, Tag 0FI4](https://stacks.math.columbia.edu/tag/0FI4)
* [Stacks Project, Tag 0FMX](https://stacks.math.columbia.edu/tag/0FMX)
* [Stacks Project, Tag 0FMY](https://stacks.math.columbia.edu/tag/0FMY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.DeRhamBaseChange Stacks.WeilCohomology
open scoped Stacks.StandardDerivedModel

universe u

attribute [local instance] Stacks.Cohomology.Generators.picardGroupAddCommGroup

namespace Stacks.DeRhamBaseChange

/-- **On the class of an invertible module, `c₁^{dR}` is the de Rham first Chern class of the
module.** -/
theorem deRhamFirstChernClassPicard_picardClassOf {X S : Scheme.{u}} (p : X ⟶ S) (L : X.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L) :
    deRhamFirstChernClassPicard p (picardClassOf X L hL) =
      AlgebraicGeometry.SheafOfModules.deRhamCohomologyFirstChernClass (X := X.toRingedSpace)
        (Scheme.Hom.deRhamAlgebras p)
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p))
        L hL := by
  exact congrArg
    (fun c => AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology
      (Scheme.Hom.deRhamAlgebras p)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p)) 2
      |>.hom.hom
      (AlgebraicGeometry.SheafOfModules.deRhamFirstChernClassAbelian (Scheme.Hom.deRhamAlgebras p)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p)) c))
    (Stacks.GluePicard.picardModelAddEquiv_classOf X.toRingedSpace L hL)

end Stacks.DeRhamBaseChange

namespace AlgebraicGeometry.SheafOfModules

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-- **A product with a class of `H^2_{dR}` vanishes once it vanishes componentwise**: if
`c ∪ a_n = 0` for every component `a_n ∈ H^{2n}_{dR}` of `a`, then `a · c = 0` in the even-degree
ring. -/
theorem evenDeRham_mul_of_eq_zero (a : evenDeRhamRing B D) (c : evenDeRhamCohomology B D 1)
    (h : ∀ n : ℕ, deRhamCohomologyCup B D ((2 * 1 : ℕ) : ℤ) ((2 * n : ℕ) : ℤ) c (a n) = 0) :
    a * DirectSum.of (evenDeRhamCohomology B D) 1 c = 0 := by
  classical
  rw [← DirectSum.sum_support_of a, Finset.sum_mul]
  refine Finset.sum_eq_zero fun n _ => ?_
  rw [DirectSum.of_mul_of]
  refine (congrArg (DirectSum.of (evenDeRhamCohomology B D) (n + 1)) ?_).trans (map_zero _)
  change reindexDeRhamCohomology B D (two_mul_add_cast n 1)
    (deRhamCohomologyCup B D _ _ (a n) c) = 0
  rw [deRhamCohomologyCup_comm, h n]
  simp only [reindexDeRhamCohomology_zero, smul_zero]

end AlgebraicGeometry.SheafOfModules

namespace Stacks.DeRhamClopen

/-- **Lemma 0FMX on the even-degree ring, for the zero scheme of a regular section.** Let `s` be a
global section of an invertible module `ℒ` on `P` whose zero scheme `D` is an effective Cartier
divisor for which the de Rham complex of log poles is defined over `S`. If every component of
`a ∈ ⨁_n H^{2n}_{dR}(P/S)` restricts to zero on `D`, then `a · c₁^{dR}(ℒ) = 0`. -/
theorem evenDeRham_mul_zeroScheme_eq_zero {P S : Scheme.{u}} (q : P ⟶ S) (L : P.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible P.presheaf P.ringCatSheaf.2 L)
    (s : L.sections)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor
      (@Stacks.Divisors.zeroScheme _ L hL (s.eval (.op ⊤))))
    (hlog : q.HasLogPolesDeRhamComplex (@Stacks.Divisors.zeroScheme _ L hL (s.eval (.op ⊤))))
    (a : evenDeRhamRing q)
    (ha : ∀ n : ℕ, deRhamPullbackSquare
      (@Stacks.Divisors.zeroScheme _ L hL (s.eval (.op ⊤))).subschemeι
      ((@Stacks.Divisors.zeroScheme _ L hL (s.eval (.op ⊤))).subschemeι ≫ q) q (𝟙 S)
      (Category.comp_id _).symm _ (a n) = 0) :
    a * DirectSum.of _ 1 (deRhamFirstChernClassPicard q (picardClassOf P L hL)) = 0 := by
  have := hD
  have : AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L := hL
  have hreg := (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection P L s).mp hD
  have hc : picardClassOf P L hL = picardClassOf P (Stacks.Divisors.invertibleSheaf'
      (@Stacks.Divisors.zeroScheme _ L hL (s.eval (.op ⊤)))) inferInstance :=
    picardClassOf_eq_of_iso P _ _ hL _ (invertibleSheafIsoZeroSchemeOfIsRegularSection L s hreg)
  have hc' : deRhamFirstChernClassPicard q (picardClassOf P L hL) =
      AlgebraicGeometry.SheafOfModules.deRhamCohomologyFirstChernClass (X := P.toRingedSpace)
        (Scheme.Hom.deRhamAlgebras q)
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras q))
        (Stacks.Divisors.invertibleSheaf'
          (@Stacks.Divisors.zeroScheme _ L hL (s.eval (.op ⊤)))) inferInstance :=
    (congrArg (deRhamFirstChernClassPicard q) hc).trans
      (deRhamFirstChernClassPicard_picardClassOf q _ _)
  rw [hc']
  refine AlgebraicGeometry.SheafOfModules.evenDeRham_mul_of_eq_zero _ _ a _ fun n => ?_
  refine Scheme.Hom.deRhamCohomologyCup_firstChernClass_eq_zero q _ hlog _ (a n) ?_
  have h := ha n
  rw [deRhamPullbackSquare_apply] at h
  have h' := congrArg (AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology
    (Scheme.Hom.deRhamAlgebras
      ((@Stacks.Divisors.zeroScheme _ L hL (s.eval (.op ⊤))).subschemeι ≫ q))
    (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras
      ((@Stacks.Divisors.zeroScheme _ L hL (s.eval (.op ⊤))).subschemeι ≫ q))) _).inv.hom h
  simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply,
    Iso.hom_inv_id_apply, map_zero] at h'
  exact h'

/-- **Condition (5) of Section 45.12 for even-degree de Rham cohomology** (Lemmas 0FMX and 0FMY,
as in the proof of Lemma 0FW9). Let `0 ⟶ ℒ ⟶ ℰ ⟶ 𝓕 ⟶ 0` be short exact on `X`, with `ℰ` and `𝓕`
finite locally free of ranks `r + 2` and `r + 1`, let `i : 𝐏(𝓕) ⟶ 𝐏(ℰ)` be the induced closed
immersion and let `𝒪_P(𝐏(𝓕))` be the divisor module of `𝐏(𝓕) ⊆ 𝐏(ℰ)`. If `a` is a class of
`⨁_n H^{2n}_{dR}(𝐏(ℰ)/B)` with `i^*a = 0`, then `a · c₁^{dR}(𝒪_P(𝐏(𝓕))) = 0`. -/
theorem evenDeRham_mul_subbundleDivisor_eq_zero {X B : Scheme.{u}} (p : X ⟶ B)
    (T : ShortComplex X.Modules) (hT : T.ShortExact) (r : ℕ)
    [hE2 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} T.X₂]
    [hE3 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} T.X₃]
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} T.X₃ (r + 1))
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} T.X₂ (r + 1 + 1))
    (L : (Stacks.Chow.bundle T.X₂).Modules)
    (hLinv : AlgebraicGeometry.SheafOfModules.IsInvertible (Stacks.Chow.bundle T.X₂).presheaf
      (Stacks.Chow.bundle T.X₂).ringCatSheaf.2 L)
    (hdiv : IsSubbundleDivisorModule T hT hE2 hE3 L hLinv) (f' : Stacks.Chow.bundle T.X₃ ⟶ B)
    (w : @Stacks.Chow.GenuineChern.bundleEmbedding X T.X₂ T.X₃ hE2 hE3 T.g hT.epi_g ≫
      (Stacks.Chow.bundleProj T.X₂ ≫ p) = f' ≫ 𝟙 B)
    (a : evenDeRhamRing (Stacks.Chow.bundleProj T.X₂ ≫ p))
    (ha : evenDeRhamPullback (@Stacks.Chow.GenuineChern.bundleEmbedding X T.X₂ T.X₃ hE2 hE3 T.g
      hT.epi_g) f' (Stacks.Chow.bundleProj T.X₂ ≫ p) (𝟙 B) w a = 0) :
    a * DirectSum.of _ 1 (deRhamFirstChernClassPicard (Stacks.Chow.bundleProj T.X₂ ≫ p)
      (picardClassOf _ L hLinv)) = 0 := by
  obtain ⟨s, hD, e, he⟩ := hdiv
  have := hF
  have := hE
  have hs2 : Smooth (Stacks.Chow.bundleProj T.X₂) := Stacks.Chow.smooth_bundleProj T.X₂ (r + 1)
  have hs3 : Smooth (Stacks.Chow.bundleProj T.X₃) := Stacks.Chow.smooth_bundleProj T.X₃ r
  have hι : (@Stacks.Divisors.zeroScheme _ L hLinv (s.eval (.op ⊤))).subschemeι =
      e.hom ≫ @Stacks.Chow.GenuineChern.bundleEmbedding X T.X₂ T.X₃ hE2 hE3 T.g hT.epi_g :=
    he.symm
  have : Smooth ((@Stacks.Divisors.zeroScheme _ L hLinv (s.eval (.op ⊤))).subschemeι ≫
      Stacks.Chow.bundleProj T.X₂) := by
    rw [hι, Category.assoc, Stacks.Chow.GenuineChern.bundleEmbedding_comp_bundleProj]
    infer_instance
  have hlog := Scheme.Hom.hasLogPolesDeRhamComplex_of_smooth (Stacks.Chow.bundleProj T.X₂) p
    (@Stacks.Divisors.zeroScheme _ L hLinv (s.eval (.op ⊤))) hD.1
  refine evenDeRham_mul_zeroScheme_eq_zero _ L hLinv s hD.1 hlog a fun n => ?_
  have hf' : f' = @Stacks.Chow.GenuineChern.bundleEmbedding X T.X₂ T.X₃ hE2 hE3 T.g hT.epi_g ≫
      (Stacks.Chow.bundleProj T.X₂ ≫ p) := by rw [w, Category.comp_id]
  have hw' : e.hom ≫ f' = ((@Stacks.Divisors.zeroScheme _ L hLinv (s.eval (.op ⊤))).subschemeι ≫
      (Stacks.Chow.bundleProj T.X₂ ≫ p)) ≫ 𝟙 B := by
    rw [hf', hι, Category.comp_id, Category.assoc]
  have hc := evenDeRhamPullback_apply_component _ _ _ _ w a n
  rw [ha, DirectSum.zero_apply] at hc
  refine (deRhamPullbackSquare_congr _ _ hι (Category.comp_id (𝟙 B)).symm _
    (by rw [Category.assoc, ← hf', hw', Category.id_comp]) _ (a n)).trans ?_
  refine (deRhamPullbackSquare_comp _ f' _ (𝟙 B) w e.hom _ (𝟙 B) hw' _ _ (a n)).symm.trans ?_
  rw [← hc, map_zero]

end Stacks.DeRhamClopen

namespace Stacks.WeilCohomology.QCQSScheme

variable {B : Scheme.{u}}

/-- **Clause (3)(c) and condition (5) of Section 45.12 for even-degree de Rham cohomology on
quasi-compact and quasi-separated schemes over `B`**, in the shape of
`Stacks.WeilCohomology.DivisorDatumClause`: the induced closed immersion `i : 𝐏(𝓕) ⟶ 𝐏(ℰ)` is a
morphism of `𝒞`, and a class `a ∈ ⨁_n H^{2n}_{dR}(𝐏(ℰ)/B)` with `i^*a = 0` is killed by
multiplication with `c₁^{dR}(𝒪_P(𝐏(𝓕)))`. -/
theorem exists_isBundleEmbedding_deRhamDivisor (X : (QCQSScheme B).FullSubcategory)
    (T : ShortComplex ((toScheme B).obj X).Modules) (hT : T.ShortExact) (r : ℕ)
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} T.X₃ (r + 1))
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} T.X₂
      (r + 1 + 1)) :
    ∃ i : (bundleObject X T.X₃ r hF).bundle ⟶ (bundleObject X T.X₂ (r + 1) hE).bundle,
      IsBundleEmbedding T hT (bundleObject X T.X₂ (r + 1) hE) (bundleObject X T.X₃ r hF) i ∧
        ∀ (L : (@Stacks.Chow.bundle ((toScheme B).obj X) T.X₂
            (bundleObject X T.X₂ (r + 1) hE).isFiniteLocallyFree).Modules)
          (hLinv : AlgebraicGeometry.SheafOfModules.IsInvertible
            (@Stacks.Chow.bundle ((toScheme B).obj X) T.X₂
              (bundleObject X T.X₂ (r + 1) hE).isFiniteLocallyFree).presheaf
            (@Stacks.Chow.bundle ((toScheme B).obj X) T.X₂
              (bundleObject X T.X₂ (r + 1) hE).isFiniteLocallyFree).ringCatSheaf.2 L),
          IsSubbundleDivisorModule T hT
              (bundleObject X T.X₂ (r + 1) hE).isFiniteLocallyFree
              (bundleObject X T.X₃ r hF).isFiniteLocallyFree L hLinv →
            ∀ a : evenDeRhamRing (bundleObject X T.X₂ (r + 1) hE).bundle.obj.hom,
              evenDeRhamPullback ((toScheme B).map i) (bundleObject X T.X₃ r hF).bundle.obj.hom
                  (bundleObject X T.X₂ (r + 1) hE).bundle.obj.hom (𝟙 B)
                  (by rw [w i, Category.comp_id]) a = 0 →
              a * DirectSum.of _ 1 (deRhamFirstChernClassPicard
                (bundleObject X T.X₂ (r + 1) hE).bundle.obj.hom
                (picardClassOf ((toScheme B).obj (bundleObject X T.X₂ (r + 1) hE).bundle)
                  ((Scheme.Modules.pullback (bundleObject X T.X₂ (r + 1) hE).iso.hom).obj L)
                  (isInvertible_pullback_obj _ L hLinv))) = 0 := by
  refine ⟨bundleEmbeddingHom T hT r hF hE, isBundleEmbedding_bundleEmbeddingHom T hT r hF hE,
    fun L hLinv hdiv a ha => ?_⟩
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree T.X₂
    (r + 1 + 1) (hM := hE)
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree T.X₃
    (r + 1) (hM := hF)
  have hid : (bundleObject X T.X₂ (r + 1) hE).iso.hom = 𝟙 _ := by
    simp only [BundleObject.iso, bundleObject, Iso.refl_hom]
    rfl
  have hc : picardClassOf ((toScheme B).obj (bundleObject X T.X₂ (r + 1) hE).bundle)
      ((Scheme.Modules.pullback (bundleObject X T.X₂ (r + 1) hE).iso.hom).obj L)
      (isInvertible_pullback_obj _ L hLinv) =
      picardClassOf (Stacks.Chow.bundle T.X₂) L hLinv :=
    picardClassOf_eq_of_iso _ _ _ _ _
      ((Scheme.Modules.pullbackCongr hid).app L ≪≫ (Scheme.Modules.pullbackId _).app L)
  rw [hc]
  exact Stacks.DeRhamClopen.evenDeRham_mul_subbundleDivisor_eq_zero X.obj.hom T hT r hF hE L
    hLinv hdiv _ _ a ha

end Stacks.WeilCohomology.QCQSScheme

end
