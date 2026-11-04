module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.FractionFieldVanishingBound
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.HigherDirectImageBaseChangeIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction

/-!
# The limit step of Gabber's Zariski–Riemann proof of Exposé XVIII-A, Corollary 1.2, as statements

Travaux de Gabber, Exposé XVIII-A, last remark of §2, proves Corollary 1.2
(`AlgebraicGeometry.Scheme.FractionFieldVanishingBound`: `cd_n(Frac B) ≤ 2e - 1` for `B` a
strictly henselian Noetherian local domain of dimension `e ≥ 1`) by passing to the limit over all
proper models `Y ⟶ Spec B` of `η = Spec (Frac B)` in the Leray spectral sequences
`E₂^{p,q}(Y) = H^p(Y, R^q j_{Y*} F) ⟹ H^{p+q}(η, F)`. This file sets up the system of models and
the transition maps of the `E₂`-terms, and splits the limit step into two precisely stated
propositions, from which Corollary 1.2 follows
(`AlgebraicGeometry.Scheme.ZariskiRiemann.fractionFieldVanishingBound_of_zariskiRiemannKilling`):

* `AlgebraicGeometry.Scheme.ZariskiRiemann.LerayKilling B` (homological algebra; true for every
  cofiltered system of factorizations of `η`): if every class of every `E₂^{p,q}(Y)` on the
  antidiagonal `p + q = m` dies in some refinement `Y' ⟶ Y`, then `H^m(η, F) = 0`. Proof sketch:
  the Leray filtration `F^q_Y ⊆ H^m(η, F)`, the image of `H^m(Y, τ_{≤ q} Rj_{Y*}F)`, satisfies
  `F^m_Y = H^m(η, F)`, `F^{-1}_Y = 0`, and `F^q_Y ⊆ F^{q-1}_{Y'}` once the image of a lift in
  `H^{m-q}(Y, R^q j_{Y*} F)` dies on `Y'`, because `τ_{≤ q} Rj_{Y*} F ⟶ Rπ_* τ_{≤ q} Rj_{Y'*} F`
  is compatible with the truncation triangles and induces the transition map on `R^q`.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.ZariskiRiemannKilling n` (the geometric content): for
  `p + q ≥ 2e` every class of `H^p(Y, R^q j_{Y*} F)` dies in some refinement. This is the
  vanishing of `colim_Y H^p(Y, R^q j_{Y*}F)`. Its proof in the source: by
  `Stacks.EtaleCohomology.sheafHIsoGeometricClosedFibreOfIsProper` the groups are
  `H^p(Y₀, (R^q j_{Y*}F)|_{Y₀})`; their colimit is `H^p(ZRS₀, A_q)` with `A_q` the limit sheaf on
  the étale topos of the closed fibre `ZRS₀` of the Zariski–Riemann space (SGA 4 VI 8.7.4), whose
  stalk at a point `v` (a valuation ring `V` of `Frac B` dominating `B`) is
  `H^q(Frac V^{sh}, F)` (Stacks 0F0R / 03Q9 in the limit). Then:
  - **Z2** (`cd` of strictly henselian valuation fields): `H^q(Frac V^{sh}, F) = 0` for
    `q > dim_ℚ (Γ_V ⊗ ℚ)`;
  - **Z1** (Abhyankar's inequality): `dim_ℚ (Γ_V ⊗ ℚ) + trdeg_k κ(V) ≤ e`, and the rational rank
    is `≥ 1` since `V` dominates `B ≠ Frac B`;
  so the stalk of `A_q` at `v` vanishes unless `trdeg_k κ(v) ≤ min(e - 1, e - q)`, i.e.
  `δ(A_q) ≤ min(e - 1, e - q)`; and Gabber's `δ`-claim `H^p(ZRS₀, A) = 0` for `p > 2δ(A)`
  reduces by SGA 4 VI 8.7.4 to the finite-type case, which is
  `AlgebraicGeometry.subsingleton_H_of_forall_mem_smallEtaleSupport_two_mul_lt`. Finally
  `p + q ≥ 2e` forces `p > 2 min(e - 1, e - q)`.

Models are all proper `f : Y ⟶ Spec B` with a point `j : η ⟶ Y` over `Spec B`; the birational
integral ones (the scheme-theoretic closure of `j`) are cofinal among them, so this is the
system of the source.

## Main definitions

* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel` — a proper model of `Spec (Frac B)` over
  `Spec B`; `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.Refinement` — a morphism of
  models.
* `Stacks.EtaleCohomology.etaleAbelianInverseImageRightDerivedDirectImageBaseChange` — the degree
  `q` base change map `g⁻¹ R^q f_* F ⟶ R^q f'_* (g')⁻¹ F` of a commutative square.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.Refinement.lerayTermMap` — the transition
  map `H^p(Y, R^q j_* F) ⟶ H^p(Y', R^q j'_* F)`.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.LerayKilling`,
  `AlgebraicGeometry.Scheme.ZariskiRiemann.ZariskiRiemannKilling` — the two halves of the limit
  step.

## Main results

* `AlgebraicGeometry.Scheme.ZariskiRiemann.fractionFieldVanishingBound_of_zariskiRiemannKilling`
  — Exposé XVIII-A, Corollary 1.2, from the two halves.

## References

* Travaux de Gabber sur l'uniformisation locale et la cohomologie étale des schémas
  quasi-excellents, Exposé XVIII-A (L. Illusie), last remark of §2, Astérisque 363–364 (2014)
* SGA 4, Exposé VI, 8.7.4
* [Stacks Project, Tag 0732](https://stacks.math.columbia.edu/tag/0732)
* [Stacks Project, Tag 0A4A](https://stacks.math.columbia.edu/tag/0A4A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (h : g' ≫ f = f' ≫ g)

/-- **The base change map of a commutative square in degree `q`.** For a commutative square
`g' ≫ f = f' ≫ g` and an abelian sheaf `F` on `X_étale`, the morphism
`g⁻¹ (R^q f_* F) ⟶ R^q f'_* ((g')⁻¹ F)`: the `q`-th cohomology sheaf of the derived base change
map `g⁻¹ Rf_* F ⟶ Rf'_* (g')⁻¹ F` ([Stacks, Tag 0A4A]), `g⁻¹` being exact. For a cartesian
square with `f` proper it is the isomorphism
`Stacks.EtaleCohomology.etaleAbelianInverseImageRightDerivedDirectImageIsoOfIsProper`. -/
def etaleAbelianInverseImageRightDerivedDirectImageBaseChange
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    (etaleAbelianInverseImage.{u, 0} g).obj
        (((etaleAbelianDirectImage.{u, 0} f).rightDerived q).obj F) ⟶
      ((etaleAbelianDirectImage.{u, 0} f').rightDerived q).obj
        ((etaleAbelianInverseImage.{u, 0} g').obj F) :=
  ((etaleAbelianInverseImage.{u, 0} g).mapIso
      (etaleAbelianRightDerivedDirectImageIsoHomology.{0, u} f q F)).hom ≫
    (((etaleAbelianInverseImage.{u, 0} g).mapDerivedCategoryHomologyIso q).app _).inv ≫
    (DerivedCategory.homologyFunctor _ q).map
      (etaleAbelianSheafDerivedBaseChange.{u, 0} f g g' f' h F) ≫
    (DerivedCategory.homologyFunctor _ q).map
      ((etaleAbelianDerivedDirectImage.{u, 0} f').map
        (((etaleAbelianInverseImage.{u, 0} g').mapDerivedCategorySingleFunctor 0).app F).hom) ≫
    (etaleAbelianRightDerivedDirectImageIsoHomology.{0, u} f' q _).inv

end Stacks.EtaleCohomology

namespace AlgebraicGeometry.Scheme.ZariskiRiemann

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

open Stacks.EtaleCohomology

variable (B : Type u) [CommRing B] [IsDomain B]

/-- **A proper model** of `η = Spec (Frac B)` over `Spec B`: a proper morphism `f : Y ⟶ Spec B`
with a point `j : η ⟶ Y` lying over the canonical map `η ⟶ Spec B`. -/
structure ProperModel where
  /-- The model. -/
  Y : Scheme.{u}
  /-- Its structure morphism. -/
  f : Y ⟶ Spec (.of B)
  [isProper : IsProper f]
  /-- The point of the model at `η`. -/
  j : Spec (.of (FractionRing B)) ⟶ Y
  fac : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B)))

attribute [instance] ProperModel.isProper

namespace ProperModel

variable {B}

/-- The point `j : η ⟶ Y` of a proper model is quasi-compact. -/
instance quasiCompact_j (M : ProperModel B) : QuasiCompact M.j := by
  have : QuasiCompact (M.j ≫ M.f) := M.fac ▸ inferInstance
  exact .of_comp M.j M.f

/-- The trivial model `Spec B` itself. -/
def base : ProperModel B where
  Y := Spec (.of B)
  f := 𝟙 _
  j := Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B)))
  fac := Category.comp_id _

/-- **A refinement** `π : M'.Y ⟶ M.Y` of a model `M` by a model `M'`: a morphism over `Spec B`
compatible with the points at `η`. -/
structure Refinement (M' M : ProperModel B) where
  /-- The morphism of models. -/
  π : M'.Y ⟶ M.Y
  comm : π ≫ M.f = M'.f
  fac : M'.j ≫ π = M.j

/-- The composite of two refinements. -/
def Refinement.comp {M'' M' M : ProperModel B} (φ' : Refinement M'' M') (φ : Refinement M' M) :
    Refinement M'' M where
  π := φ'.π ≫ φ.π
  comm := by rw [Category.assoc, φ.comm, φ'.comm]
  fac := by rw [← Category.assoc, φ'.fac, φ.fac]

/-- **The transition map of the `E₂`-terms** of the Leray spectral sequences of two models: for a
refinement `π : Y' ⟶ Y`, the map `H^p(Y, R^q j_* F) ⟶ H^p(Y', R^q j'_* F)` (with `F` read as
`(𝟙_η)⁻¹ F` on the target), inverse image along `π` on cohomology followed by the base change
map `π⁻¹ R^q j_* F ⟶ R^q j'_* F` of the square `𝟙 ≫ j = j' ≫ π`. -/
def Refinement.lerayTermMap {M' M : ProperModel B} (φ : Refinement M' M)
    (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1}) (p q : ℕ) :
    Sheaf.H.{u + 1} (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F) p →+
      Sheaf.H.{u + 1} (((etaleAbelianDirectImage.{u, 0} M'.j).rightDerived q).obj
        ((etaleAbelianInverseImage.{u, 0} (𝟙 _)).obj F)) p :=
  (Sheaf.H.map (etaleAbelianInverseImageRightDerivedDirectImageBaseChange M.j φ.π (𝟙 _) M'.j
      (by rw [Category.id_comp, φ.fac]) F q) p).comp
    (etaleCohomologyRestrictionMap.{u, 0, u + 1} φ.π
      (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F) p)

end ProperModel

/-- **The homological half of the limit step** (the colimit of the Leray spectral sequences,
read along one antidiagonal). For an abelian sheaf `F` on `η_étale` and a degree `m`: if for every
model `Y`, every `q ≤ m` and every class `c ∈ H^{m-q}(Y, R^q j_* F)` there is a refinement
`Y' ⟶ Y` killing `c`, then `H^m(η, F) = 0`. -/
def LerayKilling : Prop :=
  ∀ (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1}) (m : ℕ),
    (∀ (M : ProperModel B) (q : ℕ), q ≤ m →
      ∀ c : Sheaf.H.{u + 1} (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F) (m - q),
        ∃ (M' : ProperModel B) (φ : ProperModel.Refinement M' M),
          φ.lerayTermMap F (m - q) q c = 0) →
      Subsingleton (Sheaf.H.{u + 1} F m)

/-- **The geometric half of the limit step** (Gabber's `δ`-bound on the closed fibre of the
Zariski–Riemann space): for `B` a strictly henselian Noetherian local domain of dimension
`e ≥ 1` with `n` invertible, `F` killed by `n` on `η = Spec (Frac B)` and `p + q ≥ 2e`, every
class of `H^p(Y, R^q j_* F)` on every model `Y` dies in some refinement. -/
def ZariskiRiemannKilling (n : ℕ) : Prop :=
  ∀ (B : Type u) [CommRing B] [IsDomain B] [IsNoetherianRing B] [StrictlyHenselianLocalRing B]
    (e : ℕ), ringKrullDim B = e → 0 < e → IsUnit (n : B) →
    ∀ (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1}),
      (∀ (T : (Spec (.of (FractionRing B))).Etale) (s : F.obj.obj (op T)), n • s = 0) →
      ∀ (M : ProperModel B) (p q : ℕ), 2 * e ≤ p + q →
        ∀ c : Sheaf.H.{u + 1} (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F) p,
          ∃ (M' : ProperModel B) (φ : ProperModel.Refinement M' M), φ.lerayTermMap F p q c = 0

/-- **Exposé XVIII-A, Corollary 1.2, from the two halves of the Zariski–Riemann limit step.** -/
theorem fractionFieldVanishingBound_of_zariskiRiemannKilling {n : ℕ}
    (hZR : ZariskiRiemannKilling.{u} n)
    (hL : ∀ (B : Type u) [CommRing B] [IsDomain B] [IsNoetherianRing B]
      [StrictlyHenselianLocalRing B], LerayKilling B) :
    FractionFieldVanishingBound.{u} n := by
  intro B _ _ _ _ e he he0 hn F hF m hm
  have hm' : 2 * e - 1 < m := by exact_mod_cast hm
  exact hL B F m fun M q hq c ↦ hZR B e he he0 hn F hF M (m - q) q (by lia) c

end AlgebraicGeometry.Scheme.ZariskiRiemann

end
