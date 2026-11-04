module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.ZariskiRiemannLimitStep
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.RestrictionLongExactSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.FilteredColimitClasses

/-!
# Subsheaves of `R^q j_* F` killed by a refinement of proper models

This file supplies the homological half of the finite-level form of the limit step
(SGA 4, Exposé VI, 8.7.4, specialised to the system of proper models) in Gabber's Zariski–Riemann
proof of Travaux de Gabber, Exposé XVIII-A, Corollary 1.2.

Let `M` be a proper model of `η = Spec (Frac B)` over `Spec B`, with point `j : η ⟶ Y`, and
`G = R^q j_* F`. A morphism `ι : K ⟶ G` of abelian sheaves on `Y_étale` is **killed** by a
refinement `π : Y' ⟶ Y` if `π⁻¹ ι` followed by the base change map `π⁻¹ R^q j_* F ⟶ R^q j'_* F`
vanishes. The transition map `H^p(Y, G) ⟶ H^p(Y', R^q j'_* F)` then kills every class coming from
`H^p(Y, K)`.

Classes do come from such `K`: if `(K_i)` is a filtered system of sheaves mapping to `G` whose
colimit maps monomorphically to `G` with cokernel `Q`, and `H^p(Y, Q) = 0`, then for `Y`
quasi-compact and quasi-separated every class of `H^p(Y, G)` comes from some `H^p(Y, K_i)`: by the
long exact sequence it comes from `H^p(Y, colim K_i)`, and by [Stacks, Tag 03Q5] from a stage.

## Main definitions

* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.Refinement.Kills` — a morphism into
  `R^q j_* F` killed by a refinement.

## Main results

* `Stacks.EtaleCohomology.exists_sheafH_map_eq_of_shortExact_of_subsingleton` — for a short exact
  sequence `0 ⟶ K ⟶ G ⟶ Q ⟶ 0` with `H^p(Q) = 0`, every class of `H^p(G)` comes from `H^p(K)`.
* `Stacks.EtaleCohomology.exists_sheafH_map_eq_of_mono_colimitDesc` — the same for a filtered
  system `K_i ⟶ G` with monomorphic colimit map, on a quasi-compact quasi-separated scheme, with
  the class coming from one stage.
* `Scheme.ZariskiRiemann.ProperModel.Refinement.lerayTermMap_sheafHMap_eq_zero_of_kills`
  — a refinement killing `ι : K ⟶ R^q j_* F` kills the image of `H^p(Y, K)`.

## References

* Travaux de Gabber sur l'uniformisation locale et la cohomologie étale des schémas
  quasi-excellents, Exposé XVIII-A (L. Illusie), last remark of §2, Astérisque 363–364 (2014)
* SGA 4, Exposé VI, 8.7.4
* [Stacks Project, Tag 03Q5](https://stacks.math.columbia.edu/tag/03Q5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

/-- **A class of `H^p(G)` lifts along `K ⟶ G` when `H^p` of the cokernel vanishes.** For a short
exact sequence `0 ⟶ K ⟶ G ⟶ Q ⟶ 0` of abelian sheaves on `Y_étale` with `H^p(Y, Q) = 0`, every
class of `H^p(Y, G)` is the image of a class of `H^p(Y, K)`: the covariant long exact sequence of
`Ext` out of the constant sheaf `ℤ`. -/
theorem exists_sheafH_map_eq_of_shortExact_of_subsingleton {Y : Scheme.{u}}
    {S : ShortComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})} (hS : S.ShortExact)
    (p : ℕ) (hQ : Subsingleton (Sheaf.H.{u + 1} S.X₃ p)) (c : Sheaf.H.{u + 1} S.X₂ p) :
    ∃ x : Sheaf.H.{u + 1} S.X₁ p, Sheaf.H.map S.f p x = c := by
  obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₂ _ hS c (Subsingleton.elim _ _)
  exact ⟨x, hx⟩

/-- **A class of `H^p(G)` comes from a stage of a filtered system of subsheaves whose cokernel has
no `H^p`.** Let `Y` be quasi-compact and quasi-separated, `K : I ⥤ Sh(Y_étale)` a filtered system
with maps `ι_i : K_i ⟶ G` to an abelian sheaf `G` such that the induced map `colim K_i ⟶ G` is a
monomorphism, with cokernel `Q`. If `H^p(Y, Q) = 0`, every class of `H^p(Y, G)` is the image of a
class of some `H^p(Y, K_i)`. -/
theorem exists_sheafH_map_eq_of_mono_colimitDesc {Y : Scheme.{u}} [CompactSpace Y]
    [QuasiSeparatedSpace Y] {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (K : I ⥤ Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    {G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}} (ι : K ⟶ (Functor.const I).obj G)
    [Mono (colimit.desc K (Cocone.mk G ι))] (p : ℕ)
    (hQ : Subsingleton (Sheaf.H.{u + 1} (cokernel (colimit.desc K (Cocone.mk G ι))) p))
    (c : Sheaf.H.{u + 1} G p) :
    ∃ (i : I) (x : Sheaf.H.{u + 1} (K.obj i) p), Sheaf.H.map (ι.app i) p x = c := by
  let d := colimit.desc K (Cocone.mk G ι)
  have hS : (ShortComplex.mk d (cokernel.π d) (cokernel.condition d)).ShortExact :=
    { exact := ShortComplex.exact_cokernel d }
  obtain ⟨y, hy⟩ := exists_sheafH_map_eq_of_shortExact_of_subsingleton hS p hQ c
  obtain ⟨i, x, hx⟩ := exists_comp_mk₀_eq_of_isColimit Y K (colimit.cocone K)
    (colimit.isColimit K) p y
  refine ⟨i, x, ?_⟩
  have hι : ι.app i = colimit.ι K i ≫ d := (colimit.ι_desc (Cocone.mk G ι) i).symm
  rw [hι, Sheaf.H.map_comp_apply, Sheaf.H.map_apply (colimit.ι K i)]
  exact (congrArg (Sheaf.H.map d p) hx).trans hy

end Stacks.EtaleCohomology

namespace AlgebraicGeometry.Scheme.ZariskiRiemann

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

open Stacks.EtaleCohomology

variable {B : Type u} [CommRing B] [IsDomain B]

namespace ProperModel

/-- **A morphism into `R^q j_* F` killed by a refinement.** For a refinement `π : Y' ⟶ Y` of
proper models and a morphism `ι : K ⟶ R^q j_* F` of abelian sheaves on `Y_étale`, the composite
`π⁻¹ K ⟶ π⁻¹ R^q j_* F ⟶ R^q j'_* F` of `π⁻¹ ι` with the base change map of the square
`𝟙 ≫ j = j' ≫ π` vanishes. -/
def Refinement.Kills {M' M : ProperModel B} (φ : Refinement M' M)
    (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    {K : Sheaf M.Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (ι : K ⟶ ((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F) : Prop :=
  (etaleAbelianInverseImage.{u, 0} φ.π).map ι ≫
      etaleAbelianInverseImageRightDerivedDirectImageBaseChange M.j φ.π (𝟙 _) M'.j
        (by rw [Category.id_comp, φ.fac]) F q = 0

omit [IsDomain B] in
/-- **A refinement killing `ι : K ⟶ R^q j_* F` kills the image of `H^p(Y, K)`** in
`H^p(Y', R^q j'_* F)`: inverse image along `π` on cohomology is natural in the sheaf, so the
transition map on the image of `H^p(Y, K)` is induced by `π⁻¹ ι` followed by the base change map,
which is zero. -/
theorem Refinement.lerayTermMap_sheafHMap_eq_zero_of_kills {M' M : ProperModel B}
    (φ : Refinement M' M)
    (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1}) (p q : ℕ)
    {K : Sheaf M.Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (ι : K ⟶ ((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F)
    (h : φ.Kills F q ι) (x : Sheaf.H.{u + 1} K p) :
    φ.lerayTermMap F p q (Sheaf.H.map ι p x) = 0 := by
  simp only [Refinement.lerayTermMap, AddMonoidHom.comp_apply]
  rw [Sheaf.H.map_apply ι, etaleCohomologyRestrictionMap_comp_mk₀.{u, 0, u + 1},
    ← Sheaf.H.map_apply, ← Sheaf.H.map_comp_apply]
  rw [Refinement.Kills] at h
  rw [h, Sheaf.H.map_apply, Ext.mk₀_zero, Ext.comp_zero]

end ProperModel

end AlgebraicGeometry.Scheme.ZariskiRiemann

end
