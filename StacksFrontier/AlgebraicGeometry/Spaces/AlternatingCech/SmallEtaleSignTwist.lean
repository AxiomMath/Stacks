module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.AntiInvariantSections
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartOpenRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.AffineDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.DiagonalComplementDistinct
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationSize0265
public import StacksFrontier.RingTheory.Invariant.FreeActionTrace
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.DiagonalComplementObj
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleComparison
public import StacksFrontier.CategoryTheory.Sites.CharacterTwist
public import StacksFrontier.CategoryTheory.Sites.Modules.KoszulSectionsResolution

/-!
# The complement of the diagonals and its sign twist on the small étale site

Let `c : U ⟶ X` be an étale and separated morphism from a scheme to an algebraic space over a
scheme `S`.  The complement `W_p` of the diagonals in the `(p+1)`-fold self-product of `U` over
`X` is an algebraic space étale over `X` with a free action of the symmetric group `S_{p+1}`
[Stacks, Tag 0726]; it is represented by a scheme, so it is an étale chart of `X`, that is an
object of the small étale site of `X`.  This file reads `W_p`, its action and its projections
to `U` in the small étale site, and proves there the identification of [Stacks, Tag 0726]: the
class of a morphism `V ⟶ W_p` goes to the wedge `φ_0 ∧ ⋯ ∧ φ_p` of its components, and this
map from the sign twist of `W_p` to `∧^{p+1} ℤ[h_U]` is locally bijective.  Consequently a map
`∧^{p+1} ℤ[h_U] ⟶ F` to an abelian sheaf `F` on the small étale site is the same thing as an
`S_{p+1}`-anti-invariant section of `F` over `W_p`.

## Main definitions

* `AlgebraicGeometry.Space.SmallEtale.etaleChart`: an étale morphism from a representable
  presheaf, as an object of the small étale site.
* `AlgebraicGeometry.Space.SmallEtale.diagonalComplementChart`: `W_p` as an étale chart.
* `AlgebraicGeometry.Space.SmallEtale.diagonalComplementChartAut`: the action of `S_{p+1}`.
* `AlgebraicGeometry.Space.SmallEtale.diagonalComplementChartπ`: the projections `W_p ⟶ U`.
* `AlgebraicGeometry.Space.SmallEtale.signTwistToWedge`: the map from the sign-twisted free
  abelian presheaf on `W_p` to `∧^{p+1} ℤ[h_U]`.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.isLocallySurjective_signTwistToWedge` and
  `AlgebraicGeometry.Space.SmallEtale.isLocallyInjective_signTwistToWedge`: [Stacks, Tag 0726],
  local bijectivity.

## Implementation notes

Everything is transported from the spaces-étale site of `X`, where the geometry of `W_p` is
developed (`StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.AntiInvariantSections`), along
the comparison functor of [Stacks, Tag 03G1], which is fully faithful and a dense subsite.  Only
morphisms and covering sieves are transported, never sheaves: the abelian sheaves of the small
étale site take values in the universe of the schemes, one below those of the spaces-étale
site.

## References

* [Stacks Project, Tag 0726](https://stacks.math.columbia.edu/tag/0726)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Opposite

universe u

namespace AlgebraicGeometry.Space.SmallEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-! ### The comparison functor is fully faithful and a dense subsite -/

/-- The comparison functor from the small étale site to the spaces-étale site is fully
faithful. -/
noncomputable def comparisonFullyFaithful : (comparisonFunctor B S hS X).FullyFaithful :=
  have := comparisonFunctor_full B S hS X
  have := comparisonFunctor_faithful B S hS X
  .ofFullyFaithful _

/-- The preimage of a covering sieve of the spaces-étale site is a covering sieve of the small
étale site. -/
theorem functorPullback_mem {V : SmallEtale B S hS X.1}
    {R : Sieve ((comparisonFunctor B S hS X).obj V)}
    (hR : R ∈ SpacesEtale.topology B S hS X ((comparisonFunctor B S hS X).obj V)) :
    R.functorPullback (comparisonFunctor B S hS X) ∈ topology B S hS X.1 V := by
  have := Functor.IsDenseSubsite.isCoverDense (topology B S hS X.1)
    (SpacesEtale.topology B S hS X) (comparisonFunctor B S hS X)
  have := Functor.IsDenseSubsite.isLocallyFull (topology B S hS X.1)
    (SpacesEtale.topology B S hS X) (comparisonFunctor B S hS X)
  rw [← Functor.IsDenseSubsite.functorPushforward_mem_iff
    (J := topology B S hS X.1) (K := SpacesEtale.topology B S hS X)
    (G := comparisonFunctor B S hS X)]
  exact Functor.IsCoverDense.functorPullback_pushforward_covering ⟨R, hR⟩

/-- A chart whose image in the spaces-étale site has no points is covered by the empty sieve. -/
theorem bot_mem_topology_of_isEmpty_points {V : SmallEtale B S hS X.1}
    (hV : IsEmpty (points B S hS
      (SpacesEtale.underlying B S hS X ((comparisonFunctor B S hS X).obj V)).obj)) :
    (⊥ : Sieve V) ∈ topology B S hS X.1 V := by
  rw [← Functor.IsDenseSubsite.functorPushforward_mem_iff
    (J := topology B S hS X.1) (K := SpacesEtale.topology B S hS X)
    (G := comparisonFunctor B S hS X), Sieve.functorPushforward_bot]
  exact SpacesEtale.bot_mem_topology_of_isEmpty_points B S hS X _ hV

variable (W : BigFppfOver B S hS) (c : yoneda.obj W ⟶ X.obj) (hc : IsEtale B S hS c)

/-- An étale morphism from a representable presheaf, as an étale chart of `X`. -/
def etaleChart : SmallEtale B S hS X.1 :=
  ⟨CostructuredArrow.mk c, (isEtale_iff_presheaf_of_yoneda B S hS c).1 hc⟩

/-- The comparison functor sends the étale chart of `c` to the object of the spaces-étale site
defined by `c`. -/
theorem comparisonFunctor_obj_etaleChart :
    (comparisonFunctor B S hS X).obj (etaleChart B S hS X W c hc) =
      SpacesEtale.chartObj B S hS X W c hc :=
  rfl

variable (hsep : IsSeparated B S hS (SpacesEtale.chartObj B S hS X W c hc).obj.hom.hom) (n : ℕ)

/-- The complement of the diagonals in the `(n+1)`-fold self-product of the chart, as an object
of the spaces-étale site of `X`. -/
abbrev diagonalComplementSpace : SpacesEtale B S hS X :=
  SpacesEtale.diagonalComplement B S hS X (SpacesEtale.chartObj B S hS X W c hc) (n + 1) hsep

/-- An object of the big fppf site representing the complement of the diagonals. -/
def diagonalComplementRep : BigFppfOver B S hS :=
  (SpacesEtale.exists_siteObj_iso_underlying_diagonalComplement B S hS X
    (SpacesEtale.chartObj B S hS X W c hc) (Functor.IsRepresentable.mk' (Iso.refl _))
    n hsep).choose

/-- The identification of the presheaf represented by `diagonalComplementRep` with the
complement of the diagonals. -/
def diagonalComplementRepIso : yoneda.obj (diagonalComplementRep B S hS X W c hc hsep n) ≅
    (SpacesEtale.underlying B S hS X (diagonalComplementSpace B S hS X W c hc hsep n)).obj :=
  (SpacesEtale.exists_siteObj_iso_underlying_diagonalComplement B S hS X
    (SpacesEtale.chartObj B S hS X W c hc) (Functor.IsRepresentable.mk' (Iso.refl _))
    n hsep).choose_spec.some

/-- **The complement of the diagonals as an étale chart of `X`.** -/
def diagonalComplementChart : SmallEtale B S hS X.1 :=
  ⟨CostructuredArrow.mk ((diagonalComplementRepIso B S hS X W c hc hsep n).hom ≫
      (diagonalComplementSpace B S hS X W c hc hsep n).obj.hom.hom),
    (isEtale_iff_presheaf_of_yoneda B S hS _).1
      (isEtale_comp B S hS (isEtale_of_isIso B S hS _)
        (diagonalComplementSpace B S hS X W c hc hsep n).property)⟩

/-- The comparison functor sends the chart of the complement of the diagonals to an object
isomorphic to the complement of the diagonals. -/
def comparisonDiagonalComplementChartIso :
    (comparisonFunctor B S hS X).obj (diagonalComplementChart B S hS X W c hc hsep n) ≅
      diagonalComplementSpace B S hS X W c hc hsep n :=
  ObjectProperty.isoMk _ (Over.isoMk (ObjectProperty.isoMk _
    (diagonalComplementRepIso B S hS X W c hc hsep n)) rfl)

/-! ### The action and the projections -/

/-- **The action of the symmetric group on the chart of the complement of the diagonals**,
transported from the spaces-étale site along the fully faithful comparison functor. -/
def diagonalComplementChartAut :
    Equiv.Perm (Fin (n + 1)) →* Aut (diagonalComplementChart B S hS X W c hc hsep n) :=
  ((comparisonFullyFaithful B S hS X).autMulEquivOfFullyFaithful _).symm.toMonoidHom.comp
    ((comparisonDiagonalComplementChartIso B S hS X W c hc hsep n).conjAut.symm.toMonoidHom.comp
      (SpacesEtale.diagonalComplementAut B S hS X (SpacesEtale.chartObj B S hS X W c hc)
        (n + 1) hsep))

/-- The comparison functor carries the action of a permutation on the chart of the complement of
the diagonals to the conjugate of the corresponding action on the spaces-étale site. -/
theorem comparisonFunctor_map_diagonalComplementChartAut (σ : Equiv.Perm (Fin (n + 1))) :
    (comparisonFunctor B S hS X).map
        (diagonalComplementChartAut B S hS X W c hc hsep n σ).asIso.hom =
      (comparisonDiagonalComplementChartIso B S hS X W c hc hsep n).hom ≫
        (SpacesEtale.diagonalComplementAut B S hS X (SpacesEtale.chartObj B S hS X W c hc)
          (n + 1) hsep σ).asIso.hom ≫
        (comparisonDiagonalComplementChartIso B S hS X W c hc hsep n).inv :=
  (comparisonFullyFaithful B S hS X).map_preimage _

/-- The projection of the chart of the complement of the diagonals onto its factor of index
`i`. -/
def diagonalComplementChartπ (i : Fin (n + 1)) :
    diagonalComplementChart B S hS X W c hc hsep n ⟶ etaleChart B S hS X W c hc :=
  (comparisonFullyFaithful B S hS X).preimage
    ((comparisonDiagonalComplementChartIso B S hS X W c hc hsep n).hom ≫
      SpacesEtale.diagonalComplementπ B S hS X (SpacesEtale.chartObj B S hS X W c hc)
        (n + 1) hsep i)

/-- The comparison functor carries the projection of index `i` to the corresponding projection on
the spaces-étale site, precomposed with the comparison isomorphism. -/
theorem comparisonFunctor_map_diagonalComplementChartπ (i : Fin (n + 1)) :
    (comparisonFunctor B S hS X).map (diagonalComplementChartπ B S hS X W c hc hsep n i) =
      (comparisonDiagonalComplementChartIso B S hS X W c hc hsep n).hom ≫
        SpacesEtale.diagonalComplementπ B S hS X (SpacesEtale.chartObj B S hS X W c hc)
          (n + 1) hsep i :=
  (comparisonFullyFaithful B S hS X).map_preimage _

/-- Translating by a permutation permutes the projections. -/
theorem diagonalComplementChartAut_comp_π (σ : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 1)) :
    (diagonalComplementChartAut B S hS X W c hc hsep n σ).asIso.hom ≫
        diagonalComplementChartπ B S hS X W c hc hsep n i =
      diagonalComplementChartπ B S hS X W c hc hsep n (σ⁻¹ i) := by
  apply (comparisonFullyFaithful B S hS X).map_injective
  rw [Functor.map_comp, comparisonFunctor_map_diagonalComplementChartAut,
    comparisonFunctor_map_diagonalComplementChartπ,
    comparisonFunctor_map_diagonalComplementChartπ]
  have key : ∀ {P Q R : SpacesEtale B S hS X} (e : P ≅ Q) (a : Q ⟶ Q) (d : Q ⟶ R),
      (e.hom ≫ a ≫ e.inv) ≫ e.hom ≫ d = (e.hom ≫ a) ≫ d := by
    intros
    simp
  exact (key _ _ _).trans (SpacesEtale.comp_diagonalComplementAut_comp_π B S hS X
    (SpacesEtale.chartObj B S hS X W c hc) (n + 1) hsep
    (comparisonDiagonalComplementChartIso B S hS X W c hc hsep n).hom σ i)

/-! ### The map from the sign twist to the exterior power -/

/-- The wedge `φ_0 ∧ ⋯ ∧ φ_n` of the components of a morphism into the chart of the complement
of the diagonals. -/
def chartWedge {V : SmallEtale B S hS X.1}
    (ψ : V ⟶ diagonalComplementChart B S hS X W c hc hsep n) :
    ⋀[ℤ]^(n + 1) (FreeAbelianGroup (V ⟶ etaleChart B S hS X W c hc)) :=
  exteriorPower.ιMulti ℤ (n + 1) fun i =>
    FreeAbelianGroup.of (ψ ≫ diagonalComplementChartπ B S hS X W c hc hsep n i)

/-- Translating a morphism by a permutation `σ` multiplies its wedge by the sign of `σ`. -/
theorem chartWedge_comp_aut {V : SmallEtale B S hS X.1}
    (ψ : V ⟶ diagonalComplementChart B S hS X W c hc hsep n) (σ : Equiv.Perm (Fin (n + 1))) :
    chartWedge B S hS X W c hc hsep n
        (ψ ≫ (diagonalComplementChartAut B S hS X W c hc hsep n σ).asIso.hom) =
      ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • chartWedge B S hS X W c hc hsep n ψ := by
  have hfam : (fun i => FreeAbelianGroup.of
        ((ψ ≫ (diagonalComplementChartAut B S hS X W c hc hsep n σ).asIso.hom) ≫
          diagonalComplementChartπ B S hS X W c hc hsep n i)) =
      (fun i => FreeAbelianGroup.of (ψ ≫ diagonalComplementChartπ B S hS X W c hc hsep n i)) ∘
        (σ⁻¹ : Equiv.Perm (Fin (n + 1))) :=
    funext fun i => congrArg FreeAbelianGroup.of (by
      rw [assoc, diagonalComplementChartAut_comp_π])
  have h := AlternatingMap.map_perm (exteriorPower.ιMulti ℤ (n + 1)
      (M := FreeAbelianGroup (V ⟶ etaleChart B S hS X W c hc)))
    (fun i => FreeAbelianGroup.of (ψ ≫ diagonalComplementChartπ B S hS X W c hc hsep n i)) σ⁻¹
  rw [Equiv.Perm.sign_inv] at h
  simp only [chartWedge]
  rw [hfam, h, Units.smul_def]

/-- The sign-twisted free abelian presheaf on the chart of the complement of the diagonals. -/
abbrev chartSignTwistPresheaf : (SmallEtale B S hS X.1)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  characterTwistPresheaf (diagonalComplementChart B S hS X W c hc hsep n)
    (diagonalComplementChartAut B S hS X W c hc hsep n) Equiv.Perm.sign

/-- The exterior power `∧^{n+1} ℤ[h_U]` of the free abelian presheaf on the chart `U`. -/
abbrev chartExteriorPower : (SmallEtale B S hS X.1)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  AddCommGrpCat.presheafExteriorPower (yoneda.obj (etaleChart B S hS X W c hc) ⋙
    AddCommGrpCat.free) (n + 1)

/-- The map from the sign twist to the exterior power, on one object. -/
def signTwistToWedgeApp (V : (SmallEtale B S hS X.1)ᵒᵖ) :
    (chartSignTwistPresheaf B S hS X W c hc hsep n).obj V ⟶
      (chartExteriorPower B S hS X W c hc n).obj V :=
  AddCommGrpCat.ofHom (QuotientAddGroup.lift _
    (FreeAbelianGroup.lift fun ψ => chartWedge B S hS X W c hc hsep n ψ) (by
      intro x hx
      refine (show characterRelations (diagonalComplementChart B S hS X W c hc hsep n)
          (diagonalComplementChartAut B S hS X W c hc hsep n) Equiv.Perm.sign V.unop ≤
          (FreeAbelianGroup.lift fun ψ => chartWedge B S hS X W c hc hsep n ψ).ker from ?_) hx
      rw [characterRelations, AddSubgroup.closure_le]
      rintro y ⟨g, φ, rfl⟩
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, map_zsmul,
        FreeAbelianGroup.lift_apply_of, sub_eq_zero]
      exact chartWedge_comp_aut B S hS X W c hc hsep n φ g))

/-- The map from the sign twist to the exterior power sends the twisted generator of `ψ` to
the wedge of the components of `ψ`. -/
theorem signTwistToWedgeApp_twistedGenerator {V : SmallEtale B S hS X.1}
    (ψ : V ⟶ diagonalComplementChart B S hS X W c hc hsep n) :
    signTwistToWedgeApp B S hS X W c hc hsep n (op V)
        (twistedGenerator _ (diagonalComplementChartAut B S hS X W c hc hsep n)
          Equiv.Perm.sign ψ) =
      chartWedge B S hS X W c hc hsep n ψ :=
  FreeAbelianGroup.lift_apply_of _ _

/-- Restriction of a wedge of generators. -/
theorem chartExteriorPower_map_ιMulti_of {V V' : SmallEtale B S hS X.1} (g : V' ⟶ V)
    (a : Fin (n + 1) → (V ⟶ etaleChart B S hS X W c hc)) :
    (chartExteriorPower B S hS X W c hc n).map g.op
        (exteriorPower.ιMulti ℤ (n + 1) fun i => FreeAbelianGroup.of (a i)) =
      exteriorPower.ιMulti ℤ (n + 1) fun i => FreeAbelianGroup.of (g ≫ a i) := by
  show exteriorPower.map (n + 1)
      ((yoneda.obj (etaleChart B S hS X W c hc) ⋙ AddCommGrpCat.free).map g.op).hom.toIntLinearMap
      (exteriorPower.ιMulti ℤ (n + 1) fun i => FreeAbelianGroup.of (a i)) = _
  refine Eq.trans (exteriorPower.map_apply_ιMulti _ _) ?_
  congr 1

/-- **The map from the sign twist of the complement of the diagonals to `∧^{n+1} ℤ[h_U]`**:
the class of a morphism `V ⟶ W` goes to the wedge of its components. -/
def signTwistToWedge :
    chartSignTwistPresheaf B S hS X W c hc hsep n ⟶ chartExteriorPower B S hS X W c hc n where
  app := signTwistToWedgeApp B S hS X W c hc hsep n
  naturality := by
    intro V₁ V₂ m
    apply AddCommGrpCat.hom_ext
    refine characterRelations_hom_ext (diagonalComplementChart B S hS X W c hc hsep n)
      (diagonalComplementChartAut B S hS X W c hc hsep n) Equiv.Perm.sign _ _ fun φ => ?_
    change signTwistToWedgeApp B S hS X W c hc hsep n V₂
        (twistedGenerator _ (diagonalComplementChartAut B S hS X W c hc hsep n)
          Equiv.Perm.sign (m.unop ≫ φ)) =
      (chartExteriorPower B S hS X W c hc n).map m
        (signTwistToWedgeApp B S hS X W c hc hsep n V₁
          (twistedGenerator _ (diagonalComplementChartAut B S hS X W c hc hsep n)
            Equiv.Perm.sign φ))
    rw [signTwistToWedgeApp_twistedGenerator, signTwistToWedgeApp_twistedGenerator]
    simp only [chartWedge]
    refine Eq.trans ?_ (chartExteriorPower_map_ιMulti_of B S hS X W c hc n m.unop _).symm
    simp only [assoc]
    rfl

/-! ### Local bijectivity -/

/-- A family of morphisms into the chart all of whose pairs disagree everywhere factors through
the chart of the complement of the diagonals. -/
theorem exists_lift_diagonalComplementChart {V : SmallEtale B S hS X.1}
    (a : Fin (n + 1) → (V ⟶ etaleChart B S hS X W c hc))
    (hempty : ∀ i j : Fin (n + 1), i ≠ j →
      SpacesEtale.collisionSet B S hS X (SpacesEtale.chartObj B S hS X W c hc)
        ((comparisonFunctor B S hS X).map (a i)) ((comparisonFunctor B S hS X).map (a j)) = ∅) :
    ∃ ψ : V ⟶ diagonalComplementChart B S hS X W c hc hsep n,
      ∀ i, ψ ≫ diagonalComplementChartπ B S hS X W c hc hsep n i = a i := by
  let L := SpacesEtale.diagonalComplementLift B S hS X (SpacesEtale.chartObj B S hS X W c hc)
    (n + 1) hsep (Pi.lift fun i => (comparisonFunctor B S hS X).map (a i))
    (SpacesEtale.mem_diagonalComplementPoints_pointsMap_lift B S hS X
      (SpacesEtale.chartObj B S hS X W c hc) (n + 1) _ hempty)
  refine ⟨(comparisonFullyFaithful B S hS X).preimage
    (L ≫ (comparisonDiagonalComplementChartIso B S hS X W c hc hsep n).inv), fun i => ?_⟩
  apply (comparisonFullyFaithful B S hS X).map_injective
  rw [Functor.map_comp, Functor.FullyFaithful.map_preimage,
    comparisonFunctor_map_diagonalComplementChartπ]
  have key : ∀ {P Q R T : SpacesEtale B S hS X} (l : T ⟶ Q) (e : P ≅ Q) (d : Q ⟶ R),
      (l ≫ e.inv) ≫ e.hom ≫ d = l ≫ d := by
    intros
    simp
  refine (key _ _ _).trans ?_
  show L ≫ SpacesEtale.diagonalComplementι B S hS X _ (n + 1) hsep ≫ Pi.π _ i = _
  rw [← assoc, SpacesEtale.diagonalComplementLift_ι]
  exact Pi.lift_comp_π (fun i => (comparisonFunctor B S hS X).map (a i)) i

/-- **Stacks 0726, local surjectivity, on the small étale site.** -/
theorem isLocallySurjective_signTwistToWedge :
    Presheaf.IsLocallySurjective (topology B S hS X.1)
      (signTwistToWedge B S hS X W c hc hsep n) := by
  classical
  constructor
  intro V s
  have hgen : ∀ a : Fin (n + 1) → (V ⟶ etaleChart B S hS X W c hc),
      Presheaf.imageSieve (signTwistToWedge B S hS X W c hc hsep n)
        (exteriorPower.ιMulti ℤ (n + 1) fun i => FreeAbelianGroup.of (a i)) ∈
          topology B S hS X.1 V := by
    intro a
    obtain ⟨R, hR, hdich⟩ := SpacesEtale.exists_mem_topology_collisionSet_dichotomy B S hS X
      (SpacesEtale.chartObj B S hS X W c hc) hsep
      (fun i => (comparisonFunctor B S hS X).map (a i))
    refine (topology B S hS X.1).superset_covering ?_ (functorPullback_mem B S hS X hR)
    intro V' g hg
    by_cases hex : ∃ i j : Fin (n + 1), i ≠ j ∧ g ≫ a i = g ≫ a j
    · obtain ⟨i, j, hij, hgij⟩ := hex
      have hz : (exteriorPower.ιMulti ℤ (n + 1) fun k => FreeAbelianGroup.of (g ≫ a k)) = 0 :=
        (exteriorPower.ιMulti ℤ (n + 1)).map_eq_zero_of_eq _
          (congrArg FreeAbelianGroup.of hgij) hij
      refine ⟨0, ?_⟩
      rw [chartExteriorPower_map_ιMulti_of, hz]
      exact map_zero _
    · have hempty : ∀ i j : Fin (n + 1), i ≠ j →
          SpacesEtale.collisionSet B S hS X (SpacesEtale.chartObj B S hS X W c hc)
            ((comparisonFunctor B S hS X).map (g ≫ a i))
            ((comparisonFunctor B S hS X).map (g ≫ a j)) = ∅ := by
        intro i j hij
        rcases hdich ((comparisonFunctor B S hS X).map g) hg i j with heq | hemp
        · refine absurd ⟨i, j, hij, (comparisonFullyFaithful B S hS X).map_injective ?_⟩ hex
          rw [Functor.map_comp, Functor.map_comp]
          exact heq
        · rw [Functor.map_comp, Functor.map_comp]
          exact hemp
      obtain ⟨ψ, hψ⟩ := exists_lift_diagonalComplementChart B S hS X W c hc hsep n
        (fun i => g ≫ a i) hempty
      refine ⟨twistedGenerator _ (diagonalComplementChartAut B S hS X W c hc hsep n)
        Equiv.Perm.sign ψ, ?_⟩
      show signTwistToWedgeApp B S hS X W c hc hsep n (op V') _ = _
      rw [signTwistToWedgeApp_twistedGenerator, chartExteriorPower_map_ιMulti_of]
      exact congrArg (fun k => exteriorPower.ιMulti ℤ (n + 1) k)
        (funext fun i => congrArg FreeAbelianGroup.of (hψ i))
  let N : AddSubgroup (⋀[ℤ]^(n + 1) (FreeAbelianGroup (V ⟶ etaleChart B S hS X W c hc))) :=
    { carrier := {t | Presheaf.imageSieve (signTwistToWedge B S hS X W c hc hsep n) t ∈
        topology B S hS X.1 V}
      zero_mem' := by
        refine (topology B S hS X.1).superset_covering ?_ ((topology B S hS X.1).top_mem V)
        intro V' g _
        refine ⟨0, ?_⟩
        rw [map_zero]
        exact (map_zero _).symm
      add_mem' := fun {x y} hx hy => by
        refine (topology B S hS X.1).superset_covering ?_
          ((topology B S hS X.1).intersection_covering hx hy)
        rintro V' g ⟨⟨t₁, h₁⟩, t₂, h₂⟩
        refine ⟨t₁ + t₂, ?_⟩
        rw [map_add, h₁, h₂]
        exact (map_add _ x y).symm
      neg_mem' := fun {x} hx => by
        refine (topology B S hS X.1).superset_covering ?_ hx
        rintro V' g ⟨t, h⟩
        refine ⟨-t, ?_⟩
        rw [map_neg, h]
        exact (map_neg _ x).symm }
  have hN : N = ⊤ := by
    refine exteriorPower.eq_top_of_ιMulti_mem (n + 1) N _
      (FreeAbelianGroup.span_range_of (V ⟶ etaleChart B S hS X W c hc)) ?_
    intro m hm
    choose a ha using hm
    have hmeq : m = fun i => FreeAbelianGroup.of (a i) := funext fun i => (ha i).symm
    rw [hmeq]
    exact hgen a
  exact (hN ▸ AddSubgroup.mem_top s : s ∈ N)

/-- The image of a composite with a projection, in terms of the comparison isomorphism. -/
private theorem comparisonFunctor_map_comp_diagonalComplementChartπ {V : SmallEtale B S hS X.1}
    (ψ : V ⟶ diagonalComplementChart B S hS X W c hc hsep n) (i : Fin (n + 1)) :
    (comparisonFunctor B S hS X).map (ψ ≫ diagonalComplementChartπ B S hS X W c hc hsep n i) =
      ((comparisonFunctor B S hS X).map ψ ≫
        (comparisonDiagonalComplementChartIso B S hS X W c hc hsep n).hom) ≫
        SpacesEtale.diagonalComplementπ B S hS X (SpacesEtale.chartObj B S hS X W c hc)
          (n + 1) hsep i := by
  rw [Functor.map_comp, comparisonFunctor_map_diagonalComplementChartπ]
  rfl

/-- The components of a morphism into the chart of the complement of the diagonals are distinct
as soon as the source has a point. -/
theorem injective_comp_diagonalComplementChartπ {V : SmallEtale B S hS X.1}
    (y : points B S hS
      (SpacesEtale.underlying B S hS X ((comparisonFunctor B S hS X).obj V)).obj)
    (ψ : V ⟶ diagonalComplementChart B S hS X W c hc hsep n) :
    Function.Injective fun i => ψ ≫ diagonalComplementChartπ B S hS X W c hc hsep n i := by
  intro i j hij
  refine SpacesEtale.injective_diagonalComplementComponents B S hS X
    (SpacesEtale.chartObj B S hS X W c hc) (n + 1) hsep y
    ((comparisonFunctor B S hS X).map ψ ≫
      (comparisonDiagonalComplementChartIso B S hS X W c hc hsep n).hom) ?_
  have h := congrArg (comparisonFunctor B S hS X).map hij
  rwa [comparisonFunctor_map_comp_diagonalComplementChartπ,
    comparisonFunctor_map_comp_diagonalComplementChartπ] at h

/-- A morphism into the chart of the complement of the diagonals is determined by its
components. -/
theorem diagonalComplementChart_hom_ext {V : SmallEtale B S hS X.1}
    {ψ ψ' : V ⟶ diagonalComplementChart B S hS X W c hc hsep n}
    (h : ∀ i, ψ ≫ diagonalComplementChartπ B S hS X W c hc hsep n i =
      ψ' ≫ diagonalComplementChartπ B S hS X W c hc hsep n i) : ψ = ψ' := by
  apply (comparisonFullyFaithful B S hS X).map_injective
  rw [← cancel_mono (comparisonDiagonalComplementChartIso B S hS X W c hc hsep n).hom]
  refine SpacesEtale.eq_of_diagonalComplementComponents_eq B S hS X
    (SpacesEtale.chartObj B S hS X W c hc) (n + 1) hsep (funext fun i => ?_)
  have hi := congrArg (comparisonFunctor B S hS X).map (h i)
  rwa [comparisonFunctor_map_comp_diagonalComplementChartπ,
    comparisonFunctor_map_comp_diagonalComplementChartπ] at hi

/-- **Stacks 0726, local injectivity, on the small étale site.** -/
theorem isLocallyInjective_signTwistToWedge :
    Presheaf.IsLocallyInjective (topology B S hS X.1)
      (signTwistToWedge B S hS X W c hc hsep n) := by
  constructor
  intro V x₁ x₂ hx
  by_cases hpt : Nonempty (points B S hS
      (SpacesEtale.underlying B S hS X ((comparisonFunctor B S hS X).obj V.unop)).obj)
  · obtain ⟨y⟩ := hpt
    obtain ⟨z₁, rfl⟩ := QuotientAddGroup.mk_surjective x₁
    obtain ⟨z₂, rfl⟩ := QuotientAddGroup.mk_surjective x₂
    let rel := characterRelations (diagonalComplementChart B S hS X W c hc hsep n)
      (diagonalComplementChartAut B S hS X W c hc hsep n) Equiv.Perm.sign V.unop
    have hsub : (QuotientAddGroup.mk (z₁ - z₂) :
        ToType ((chartSignTwistPresheaf B S hS X W c hc hsep n).obj V)) = 0 := by
      refine FreeAbelianGroup.eq_zero_of_wedge_eq_zero
        (fun ψ i => ψ ≫ diagonalComplementChartπ B S hS X W c hc hsep n i)
        (injective_comp_diagonalComplementChartπ B S hS X W c hc hsep n y)
        (QuotientAddGroup.mk' rel) ?_
        ((ConcreteCategory.hom ((signTwistToWedge B S hS X W c hc hsep n).app V)).comp
          (QuotientAddGroup.mk' rel)) (fun a => signTwistToWedgeApp_twistedGenerator
            B S hS X W c hc hsep n a) (z₁ - z₂) ?_
      · intro a b σ hab
        have hcomp : a = b ≫ (diagonalComplementChartAut B S hS X W c hc hsep n σ⁻¹).asIso.hom := by
          refine diagonalComplementChart_hom_ext B S hS X W c hc hsep n fun i => ?_
          rw [assoc, diagonalComplementChartAut_comp_π, inv_inv]
          exact congrFun hab i
        have hgen := twistedGenerator_act (diagonalComplementChart B S hS X W c hc hsep n)
          (diagonalComplementChartAut B S hS X W c hc hsep n) Equiv.Perm.sign b σ⁻¹
        rw [Equiv.Perm.sign_inv] at hgen
        rw [hcomp]
        exact hgen
      · exact (map_sub ((ConcreteCategory.hom
          ((signTwistToWedge B S hS X W c hc hsep n).app V)).comp (QuotientAddGroup.mk' rel))
          z₁ z₂).trans (sub_eq_zero.2 hx)
    have h2 : (QuotientAddGroup.mk z₁ :
        ToType ((chartSignTwistPresheaf B S hS X W c hc hsep n).obj V)) =
        QuotientAddGroup.mk z₂ := by
      rw [← sub_eq_zero]
      exact (map_sub (QuotientAddGroup.mk' rel) z₁ z₂).symm.trans hsub
    refine (topology B S hS X.1).superset_covering ?_ ((topology B S hS X.1).top_mem V.unop)
    exact le_of_eq ((Presheaf.equalizerSieve_eq_top_iff _ _).2 h2).symm
  · refine (topology B S hS X.1).superset_covering bot_le ?_
    exact bot_mem_topology_of_isEmpty_points B S hS X (not_nonempty_iff.1 hpt)

/-! ### Maps out of the exterior power are anti-invariant sections -/

/-- The sheafification of the map from the sign twist to the exterior power is an
isomorphism. -/
theorem isIso_presheafToSheaf_map_signTwistToWedge :
    IsIso ((presheafToSheaf (topology B S hS X.1) AddCommGrpCat.{u}).map
      (signTwistToWedge B S hS X W c hc hsep n)) := by
  have hi : Sheaf.IsLocallyInjective ((presheafToSheaf (topology B S hS X.1)
      AddCommGrpCat.{u}).map (signTwistToWedge B S hS X W c hc hsep n)) :=
    (Presheaf.isLocallyInjective_presheafToSheaf_map_iff (topology B S hS X.1) _).2
      (isLocallyInjective_signTwistToWedge B S hS X W c hc hsep n)
  have hs : Sheaf.IsLocallySurjective ((presheafToSheaf (topology B S hS X.1)
      AddCommGrpCat.{u}).map (signTwistToWedge B S hS X W c hc hsep n)) :=
    (Presheaf.isLocallySurjective_presheafToSheaf_map_iff (topology B S hS X.1) _).2
      (isLocallySurjective_signTwistToWedge B S hS X W c hc hsep n)
  exact (Sheaf.isLocallyBijective_iff_isIso _).1 ⟨hi, hs⟩

/-- **Stacks 0726 on the small étale site.**  A map from `∧^{n+1} ℤ[h_U]` to an abelian sheaf
`G` is the same thing as an `S_{n+1}`-anti-invariant section of `G` over the chart of the
complement of the diagonals: precompose with the map from the sign twist, which becomes an
isomorphism after sheafification, and read the result as a section transforming according to
the sign character. -/
def wedgeHomEquiv (G : Sheaf (topology B S hS X.1) AddCommGrpCat.{u}) :
    (chartExteriorPower B S hS X W c hc n ⟶ G.obj) ≃+
      characterSections (diagonalComplementChart B S hS X W c hc hsep n)
        (diagonalComplementChartAut B S hS X W c hc hsep n) Equiv.Perm.sign G.obj :=
  AddEquiv.ofBijective
    (AddMonoidHom.mk' (fun f => characterTwistPresheafHomEquiv _ _ _ G.obj
        (signTwistToWedge B S hS X W c hc hsep n ≫ f)) fun f f' => by
        refine Subtype.ext ?_
        simp only [characterTwistPresheafHomEquiv_apply, Preadditive.comp_add]
        rfl)
    (by
      have := isIso_presheafToSheaf_map_signTwistToWedge B S hS X W c hc hsep n
      let a := sheafificationAdjunction (topology B S hS X.1) AddCommGrpCat.{u}
      let σ := signTwistToWedge B S hS X W c hc hsep n
      let L := presheafToSheaf (topology B S hS X.1) AddCommGrpCat.{u}
      have hpre : Function.Bijective (fun f : chartExteriorPower B S hS X W c hc n ⟶ G.obj =>
          σ ≫ f) := by
        refine ⟨fun f f' h => ?_, fun g => ?_⟩
        · apply (a.homEquiv _ G).symm.injective
          apply (cancel_epi (L.map σ)).1
          rw [← Adjunction.homEquiv_naturality_left_symm,
            ← Adjunction.homEquiv_naturality_left_symm]
          exact congrArg _ h
        · refine ⟨a.homEquiv _ G (inv (L.map σ) ≫ (a.homEquiv _ G).symm g), ?_⟩
          change σ ≫ a.homEquiv _ G _ = g
          rw [← Adjunction.homEquiv_naturality_left, IsIso.hom_inv_id_assoc,
            Equiv.apply_symm_apply]
      exact (characterTwistPresheafHomEquiv _ _ _ G.obj).bijective.comp hpre)

/-- The section attached to a morphism `f` out of the exterior power is the value of `f` on the
image of the twisted generator of the identity. -/
theorem wedgeHomEquiv_apply (G : Sheaf (topology B S hS X.1) AddCommGrpCat.{u})
    (f : chartExteriorPower B S hS X W c hc n ⟶ G.obj) :
    ((wedgeHomEquiv B S hS X W c hc hsep n G f : characterSections _ _ _ G.obj) :
        G.obj.obj (op (diagonalComplementChart B S hS X W c hc hsep n))) =
      f.app _ (signTwistToWedge B S hS X W c hc hsep n |>.app _
        (twistedGenerator _ (diagonalComplementChartAut B S hS X W c hc hsep n)
          Equiv.Perm.sign (𝟙 _))) :=
  rfl

/-! ### Affineness of the complement of the diagonals -/

/-- The structure morphism of the chart of the complement of the diagonals is affine as soon as
that of the chart is. -/
theorem isAffineHom_diagonalComplementChart_hom (hcA : IsAffineHom B S hS c) :
    IsAffineHom B S hS (diagonalComplementChart B S hS X W c hc hsep n).obj.hom :=
  isAffineHom_comp B S hS _ _
    (isAffineHom_of_isIso (diagonalComplementRepIso B S hS X W c hc hsep n).hom)
    (SpacesEtale.isAffineHom_diagonalComplement_hom (SpacesEtale.chartObj B S hS X W c hc) hcA n
      hsep)

/-- **The complement of the diagonals in a self-product of an affine chart, affine over a
separated space, is an affine scheme.**  Its projection to the chart is affine, being a morphism
over `X` between objects affine over `X` with separated target, and the chart is affine. -/
theorem isAffine_chartScheme_diagonalComplementChart
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W)) (hcA : IsAffineHom B S hS c) :
    IsAffine (chartScheme (diagonalComplementChart B S hS X W c hc hsep n)) := by
  let π₀ := diagonalComplementChartπ B S hS X W c hc hsep n 0
  have hπ : IsAffineHom B S hS (yoneda.map ((SmallEtale.toOver B S hS X.1).map π₀)) := by
    refine isAffineHom_of_isAffineHom_comp_of_isSeparated B S hS _
      (etaleChart B S hS X W c hc).obj.hom ?_ hsep
    rw [yoneda_map_toOver_map_comp_hom]
    exact isAffineHom_diagonalComplementChart_hom B S hS X W c hc hsep n hcA
  obtain ⟨W', p, q, hpq⟩ := hπ ⟨W, hW⟩ (𝟙 _)
  have hp : IsIso p := hpq.isIso_fst_of_isIso (IsIso.id _)
  let e : (BigAffineFppf.inclusion B S hS).obj W' ≅
      (SmallEtale.toOver B S hS X.1).obj (diagonalComplementChart B S hS X W c hc hsep n) :=
    (Functor.FullyFaithful.ofFullyFaithful yoneda).preimageIso (asIso p)
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj W')) :=
    W'.property
  exact IsAffine.of_isIso ((BigFppfOver.toScheme B S hS).mapIso e).inv

/-! ### The action is free, and has a trace-one function -/

/-- The presheaf morphism underlying the image of a morphism of charts in the spaces-étale site
is the Yoneda image of its underlying morphism. -/
theorem toSpaces_map_comparisonFunctor_map_hom {V V' : SmallEtale B S hS X.1} (f : V ⟶ V') :
    ((SpacesEtale.toSpaces B S hS X).map ((comparisonFunctor B S hS X).map f)).hom =
      yoneda.map ((SmallEtale.toOver B S hS X.1).map f) :=
  rfl

/-- **No nontrivial permutation fixes a field-valued point of the complement of the
diagonals.**  If a ring map `ψ` from the functions on the chart of the complement of the
diagonals to a field is invariant under `σ`, then `σ = 1`: the corresponding point of the
complement would have two equal components. -/
theorem eq_one_of_appTop_comp_eq {K : Type u} [Field K]
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W)) (hcA : IsAffineHom B S hS c)
    (σ : Equiv.Perm (Fin (n + 1)))
    (ψ : Γ(chartScheme (diagonalComplementChart B S hS X W c hc hsep n), ⊤) ⟶ CommRingCat.of K)
    (hψ : Function.Surjective ψ)
    (hfix : (chartSchemeMap
        (diagonalComplementChartAut B S hS X W c hc hsep n σ).asIso.hom).appTop ≫ ψ = ψ) :
    σ = 1 := by
  have := isAffine_chartScheme_diagonalComplementChart B S hS X W c hc hsep n hW hcA
  let V := diagonalComplementChart B S hS X W c hc hsep n
  let Y := chartScheme V
  let ι : Spec (.of K) ⟶ Y := Spec.map ψ ≫ Y.isoSpec.inv
  have : AlgebraicGeometry.IsClosedImmersion (Spec.map ψ) :=
    IsClosedImmersion.spec_of_surjective ψ hψ
  have hK : B.Contains (Spec (.of K)) :=
    B.contains_of_mono_of_isSeparated ι ((SmallEtale.toOver B S hS X.1).obj V).left.property
  let b : Spec (.of K) ⟶ S := ι ≫ B.inclusion.map ((SmallEtale.toOver B S hS X.1).obj V).hom
  let T := BigFppfOver.mk B S hS hK b
  let ιT : T ⟶ (SmallEtale.toOver B S hS X.1).obj V := Over.homMk (ObjectProperty.homMk ι) rfl
  -- the point is fixed by `σ`
  have hιfix : ιT ≫ (SmallEtale.toOver B S hS X.1).map
      (diagonalComplementChartAut B S hS X W c hc hsep n σ).asIso.hom = ιT := by
    apply (BigFppfOver.toScheme B S hS).map_injective
    rw [Functor.map_comp]
    show ι ≫ chartSchemeMap (diagonalComplementChartAut B S hS X W c hc hsep n σ).asIso.hom = ι
    simp only [ι, assoc]
    rw [← Scheme.isoSpec_inv_naturality, ← assoc, ← Spec.map_comp, hfix]
  by_contra hσ
  obtain ⟨i, hi⟩ : ∃ i : Fin (n + 1), σ⁻¹ i ≠ i := by
    by_contra hall
    exact hσ (inv_eq_one.1 (Equiv.ext fun i => not_ne_iff.1 (fun h => hall ⟨i, h⟩)))
  -- a point of the field spectrum
  obtain ⟨t, -⟩ := surjective_pointsToScheme B S hS T
    (Nonempty.some (inferInstance : Nonempty (Spec (.of K))))
  let g := yoneda.map ιT ≫ (diagonalComplementRepIso B S hS X W c hc hsep n).hom
  refine SpacesEtale.comp_diagonalComplementπ_ne B S hS X (SpacesEtale.chartObj B S hS X W c hc)
    (n + 1) hsep g t (Ne.symm hi) ?_
  -- `g` is fixed by the action, which permutes the projections
  set θ := diagonalComplementRepIso B S hS X W c hc hsep n with hθ
  let autₚ := ((SpacesEtale.toSpaces B S hS X).map (SpacesEtale.diagonalComplementAut B S hS X
      (SpacesEtale.chartObj B S hS X W c hc) (n + 1) hsep σ).asIso.hom).hom
  have h : yoneda.map ((SmallEtale.toOver B S hS X.1).map
      (diagonalComplementChartAut B S hS X W c hc hsep n σ).asIso.hom) = θ.hom ≫ autₚ ≫ θ.inv :=
    congrArg (fun k => ((SpacesEtale.toSpaces B S hS X).map k).hom)
      (comparisonFunctor_map_diagonalComplementChartAut B S hS X W c hc hsep n σ)
  have aux : ∀ {C : Type (u + 1)} [Category.{u + 1} C] {T A Y : C} (ι : T ⟶ A) (s : A ⟶ A)
      (θ : A ≅ Y) (a : Y ⟶ Y), s = θ.hom ≫ a ≫ θ.inv → ι ≫ s = ι →
        (ι ≫ θ.hom) ≫ a = ι ≫ θ.hom := by
    intro C _ T A Y ι s θ a hs hι
    calc (ι ≫ θ.hom) ≫ a = ι ≫ (θ.hom ≫ a ≫ θ.inv) ≫ θ.hom := by simp
      _ = ι ≫ s ≫ θ.hom := by rw [hs]
      _ = ι ≫ θ.hom := by rw [← assoc, hι]
  have hg : g ≫ autₚ = g :=
    aux (yoneda.map ιT) _ θ autₚ h (by rw [← Functor.map_comp, hιfix])
  let πₚ : Fin (n + 1) → ((SpacesEtale.underlying B S hS X
      (diagonalComplementSpace B S hS X W c hc hsep n)).obj ⟶ yoneda.obj W) := fun k =>
    ((SpacesEtale.toSpaces B S hS X).map (SpacesEtale.diagonalComplementπ B S hS X
      (SpacesEtale.chartObj B S hS X W c hc) (n + 1) hsep k)).hom
  have hπ : autₚ ≫ πₚ i = πₚ (σ⁻¹ i) := by
    have := SpacesEtale.comp_diagonalComplementAut_comp_π B S hS X
      (SpacesEtale.chartObj B S hS X W c hc) (n + 1) hsep (𝟙 _) σ i
    simp only [id_comp] at this
    exact congrArg (fun k => ((SpacesEtale.toSpaces B S hS X).map k).hom) this
  show g ≫ πₚ i = g ≫ πₚ (σ⁻¹ i)
  rw [← hπ, ← assoc, hg]

/-- The pullback of functions along the action of a permutation on the chart of the complement
of the diagonals. -/
abbrev autPullback (σ : Equiv.Perm (Fin (n + 1))) :
    Γ(chartScheme (diagonalComplementChart B S hS X W c hc hsep n), ⊤) →+*
      Γ(chartScheme (diagonalComplementChart B S hS X W c hc hsep n), ⊤) :=
  (chartSchemeMap (diagonalComplementChartAut B S hS X W c hc hsep n σ).asIso.hom).appTop.hom

/-- Pulling back along the identity permutation is the identity. -/
theorem autPullback_one : autPullback B S hS X W c hc hsep n 1 = RingHom.id _ := by
  ext a
  simp only [autPullback, map_one]
  show (chartSchemeMap (𝟙 (diagonalComplementChart B S hS X W c hc hsep n))).appTop.hom a = a
  simp [chartSchemeMap]

/-- Pulling back along `σ * τ` is pulling back along `σ` and then along `τ`. -/
theorem autPullback_mul (σ τ : Equiv.Perm (Fin (n + 1))) (a) :
    autPullback B S hS X W c hc hsep n (σ * τ) a =
      autPullback B S hS X W c hc hsep n τ (autPullback B S hS X W c hc hsep n σ a) := by
  simp only [autPullback, map_mul, Aut.mul_asIso]
  show (chartSchemeMap ((diagonalComplementChartAut B S hS X W c hc hsep n τ).asIso.hom ≫
    (diagonalComplementChartAut B S hS X W c hc hsep n σ).asIso.hom)).appTop.hom a = _
  simp only [chartSchemeMap, Functor.map_comp, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
    RingHom.coe_comp, Function.comp_apply]

/-- **A trace-one function for the action of the symmetric group on the complement of the
diagonals.**  The action is free on the affine scheme `W_n`, so the trace of some function is
`1`. -/
theorem exists_sum_autPullback_eq_one
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W)) (hcA : IsAffineHom B S hS c) :
    ∃ t : Γ(chartScheme (diagonalComplementChart B S hS X W c hc hsep n), ⊤),
      ∑ σ : Equiv.Perm (Fin (n + 1)), autPullback B S hS X W c hc hsep n σ t = 1 := by
  classical
  let A := Γ(chartScheme (diagonalComplementChart B S hS X W c hc hsep n), ⊤)
  let act : MulSemiringAction (Equiv.Perm (Fin (n + 1))) A :=
    { smul := fun σ a => autPullback B S hS X W c hc hsep n σ⁻¹ a
      one_smul := fun a => by
        show autPullback B S hS X W c hc hsep n 1⁻¹ a = a
        rw [inv_one, autPullback_one]
        rfl
      mul_smul := fun σ τ a => by
        show autPullback B S hS X W c hc hsep n (σ * τ)⁻¹ a =
          autPullback B S hS X W c hc hsep n σ⁻¹ (autPullback B S hS X W c hc hsep n τ⁻¹ a)
        rw [mul_inv_rev, autPullback_mul]
      smul_zero := fun σ => map_zero _
      smul_add := fun σ a b => map_add _ a b
      smul_one := fun σ => map_one _
      smul_mul := fun σ a b => map_mul _ a b }
  have hfree : ∀ σ : Equiv.Perm (Fin (n + 1)), σ ≠ 1 →
      Ideal.span (Set.range fun a : A => σ • a - a) = ⊤ := by
    intro σ hσ
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    let := Ideal.Quotient.field m
    let ψ : A ⟶ CommRingCat.of (A ⧸ m) := CommRingCat.ofHom (Ideal.Quotient.mk m)
    have hσ' : σ⁻¹ = 1 := by
      refine eq_one_of_appTop_comp_eq B S hS X W c hc hsep n hW hcA σ⁻¹ ψ
        Ideal.Quotient.mk_surjective ?_
      ext a
      show Ideal.Quotient.mk m (autPullback B S hS X W c hc hsep n σ⁻¹ a) =
        Ideal.Quotient.mk m a
      rw [Ideal.Quotient.eq]
      exact hle (Ideal.subset_span ⟨a, rfl⟩)
    exact hσ (inv_eq_one.1 hσ')
  obtain ⟨t, ht⟩ := MulSemiringAction.exists_sum_smul_eq_one hfree
  refine ⟨t, ?_⟩
  rw [← ht]
  exact Fintype.sum_equiv (Equiv.inv _) _ _ (fun σ => by
    show autPullback B S hS X W c hc hsep n σ t = autPullback B S hS X W c hc hsep n σ⁻¹⁻¹ t
    rw [inv_inv])

end AlgebraicGeometry.Space.SmallEtale
