module

public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineHypercoverRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleEquiUniverseModel
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModelFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.CoveringSetFromCoversTop
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.CoveringSetTransport

/-!
# Hom out of a finitely presented module and filtered colimits on a space

Let `X` be a quasi-compact and quasi-separated algebraic space over a scheme `S`, let `G` be an
`𝒪_X`-module of finite presentation and let `λ ↦ F_λ` be a filtered system of `𝒪_X`-modules.
Stacks 07U7 asserts

`colim_λ Hom_X(G, F_λ) = Hom_X(G, colim_λ F_λ)`.

The proof is the one of the source: the equality is the case of Stacks 0GN0 for the small étale
ringed site, and its site hypothesis — the condition of Stacks 0GMR part (4) — is checked for the
set of *affine* objects of `X_étale` through conditions (2)(a), (2)(b), (2)(c) of Stacks 0GMS.

Those conditions live at the canonical sheaf universe of the site, and Stacks 0GN0 is available
only for an `AlgebraicGeometry.RingedSite.{u, u, u}`, whereas
`AlgebraicGeometry.Space.smallEtaleRingedSite` is an `AlgebraicGeometry.RingedSite.{u + 1, u, u}`.
They are therefore checked on the equi-universe model
`AlgebraicGeometry.Space.smallEtaleModelRingedSite`, and the conclusion is read back onto the
`𝒪_X`-modules of the space across `AlgebraicGeometry.Space.modulesEquivModelModules`.

## Main definitions

* `AlgebraicGeometry.Space.SmallEtaleModel.affineObjects`: the objects of the model whose image
  in the small étale site is an affine étale chart. This is the set `B` of Stacks 0GMS case (2).

## Main results

* `AlgebraicGeometry.Space.preservesColimitsOfShape_coyoneda_of_isFinitePresentation`:
  **Stacks 07U7**, stated for `AlgebraicGeometry.Space.Modules` on the small étale ringed site of
  the space itself.
* `AlgebraicGeometry.Space.SmallEtaleModel`
  `.exists_set_isLocallySurjective_and_isQuasiCompact_prod_self`: the hypothesis of Stacks 0GMR
  part (4) for the model.
* `AlgebraicGeometry.Space.SmallEtaleModel.exists_finite_affineObjects_isLocallySurjective`,
  `…exists_finite_affine_hypercover_hom` and
  `…exists_finite_affineObjects_isLocallySurjective_prod`: **conditions (2)(a), (2)(b) and
  (2)(c) of Stacks 0GMS on the model.**
* `AlgebraicGeometry.Space.SmallEtale.exists_affineObject_singleton_mem_precoverage`: an object of
  the small étale site with quasi-compact underlying scheme is covered by a single affine object.
* `AlgebraicGeometry.Space.SmallEtale.compactSpace_prod`: Stacks 073B on charts — the product of
  two quasi-compact objects of the small étale site of a quasi-separated space is quasi-compact.

## Implementation notes

Stacks 0GMS case (2) is
`CategoryTheory.Sheaf.exists_set_isLocallySurjective_and_isQuasiCompact_prod_self`, and the three
conditions are its inputs. `SmallEtale.compactSpace_prod` is the chart form of Stacks 073B given by
Morphisms of Spaces, Lemma 67.8.10, specialised to étale charts of the space itself.

Quasi-separatedness is `AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated`, which is
quasi-separatedness over the terminal scheme, and so takes the containment `hZ` of that scheme
positionally; quasi-compactness is `AlgebraicGeometry.Space.IsQuasiCompactSpace`. The module
universe is the universe `u` of the schemes, as in the rest of the algebraic-spaces development.

Condition (2)(a) is obtained from the affine étale surjective chart of Stacks 03H6: that chart,
read as an object of the small étale site, covers the site by itself
(`AlgebraicGeometry.Space.SmallEtale.coversTop_of_isSurjective`), and
`CategoryTheory.Sheaf.isLocallySurjective_terminal_from_sigma_sheafifiedYoneda` turns covering the
final object into surjectivity onto the final sheaf. The passage from the representable
surjectivity that Stacks 03H6 produces to the point-set surjectivity that
`coversTop_of_isSurjective` consumes is Stacks 03H5,
`AlgebraicGeometry.Space.presheafSurjective_iff_isSurjective_yoneda`. The index type of a
one-element family has to be moved from `Type (u + 1)`, where `coversTop_of_isSurjective` leaves
it, down to `Type u`, where Stacks 0GMS case (2) on the model wants it; `coversTop_punit` does
that, a constant family's `Sieve.ofObjects` depending only on its single value.

Condition (2)(b) is the transport of
`AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_refinement`, the *sieve-level* form of
Stacks 0218 on the small étale site, along `AlgebraicGeometry.Space.smallEtaleModelEquivalence`;
the hypercover packaging is that of
`AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_hypercover_hom`. The transport itself is
`CategoryTheory.Sieve.ofArrows_inverse_mem` and `CategoryTheory.Sieve.ofArrows_inverse_le`.

Condition (2)(c) is a one-element family. The product of two objects of the model is carried by
`CategoryTheory.Limits.PreservesLimitPair.iso` to the product of the small étale site, which is
the fibre product of the two charts over the space and is quasi-compact by `compactSpace_prod`;
one affine object covers it by `exists_affineObject_singleton_mem_precoverage`; and the covering
transports back to the model by `Sieve.ofArrows_inverse_mem`. The surjection of sheaves that the
source asks for is then
`CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_prodLift_of_mem`, the two morphisms being the
covering arrow followed by the two projections — so that `prod.lift` of them is the covering
arrow itself.

That a surjective étale morphism of schemes over the space generates a covering sieve of its
target *as an object of* the small étale site is
`AlgebraicGeometry.BigFppfSite.singleton_mem_etalePrecoverage` read through
`AlgebraicGeometry.Space.SmallEtale.precoverage_eq_comap`.

Finite presentation is carried across the model equivalence by
`AlgebraicGeometry.Space.isFinitePresentation_modulesEquivModelModules`.

## References

* [Stacks Project, Tag 07U7](https://stacks.math.columbia.edu/tag/07U7)
* [Stacks Project, Tag 0GN0](https://stacks.math.columbia.edu/tag/0GN0)
* [Stacks Project, Tag 0GMR](https://stacks.math.columbia.edu/tag/0GMR)
* [Stacks Project, Tag 0GMS](https://stacks.math.columbia.edu/tag/0GMS)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 03H5](https://stacks.math.columbia.edu/tag/03H5)
* [Stacks Project, Tag 073B](https://stacks.math.columbia.edu/tag/073B)
* [Stacks Project, Tag 0218](https://stacks.math.columbia.edu/tag/0218)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.GrothendieckTopology

universe a b v u

/-- A one-element family covering the final object does so at any index universe. -/
theorem coversTop_punit {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {U : C}
    (h : J.CoversTop fun _ : PUnit.{a + 1} => U) :
    J.CoversTop fun _ : PUnit.{b + 1} => U := by
  intro X
  refine J.superset_covering ?_ (h X)
  rintro V g hg
  obtain ⟨-, ⟨b⟩⟩ := (Sieve.mem_ofObjects_iff _ g).1 hg
  exact (Sieve.mem_ofObjects_iff _ g).2 ⟨PUnit.unit, ⟨b⟩⟩

end CategoryTheory.GrothendieckTopology

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- The objects of the equi-universe model of the small étale site whose image in the small
étale site has affine underlying scheme. This is the set `B` of Stacks 0GMS case (2). -/
def SmallEtaleModel.affineObjects : Set (SmallEtaleModel B S hS F) :=
  {W | (smallEtaleModelEquivalence B S hS F).functor.obj W ∈ SmallEtale.affineObjects B S hS F}

/-- An object of the model lies in `SmallEtaleModel.affineObjects` exactly when its image in
the small étale site lies in `SmallEtale.affineObjects`. -/
@[simp]
theorem SmallEtaleModel.mem_affineObjects_iff {W : SmallEtaleModel B S hS F} :
    W ∈ SmallEtaleModel.affineObjects B S hS F ↔
      (smallEtaleModelEquivalence B S hS F).functor.obj W ∈
        SmallEtale.affineObjects B S hS F :=
  Iff.rfl

variable (hF : IsAlgebraicSpace B S hS F)

/-- The image under the inverse of the model equivalence of an affine object of the small étale
site is an affine object of the model. -/
private theorem mem_affineObjects_inverse_obj_aux {U : SmallEtale B S hS F}
    (hU : U ∈ SmallEtale.affineObjects B S hS F) :
    (smallEtaleModelEquivalence B S hS F).inverse.obj U ∈
      SmallEtaleModel.affineObjects B S hS F := by
  have hiso : (smallEtaleModelEquivalence B S hS F).functor.obj
      ((smallEtaleModelEquivalence B S hS F).inverse.obj U) ≅ U :=
    (smallEtaleModelEquivalence B S hS F).counitIso.app U
  have _ : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U) := hU
  exact IsAffine.of_isIso
    (((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).mapIso hiso).hom)

include hF

/-- The affine étale surjective chart of Stacks 03H6, read as an object of the small étale
site of a quasi-compact algebraic space, together with the fact that it covers the site by
itself. -/
theorem SmallEtale.exists_affineObject_coversTop (hqc : IsQuasiCompactSpace B S hS F) :
    ∃ U : SmallEtale B S hS F, U ∈ SmallEtale.affineObjects B S hS F ∧
      (SmallEtale.topology B S hS F).CoversTop fun _ : PUnit.{u + 2} => U := by
  obtain ⟨U, a, hUaff, hasurj, haet⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS F hF).mp hqc
  refine ⟨⟨CostructuredArrow.mk a, presheaf_etale_of_isEtale B S hS haet⟩, hUaff, ?_⟩
  exact SmallEtale.coversTop_of_isSurjective B S hS F hF _
    ((presheafSurjective_iff_isSurjective_yoneda B S hS F hF U a).1 hasurj)

/-- **Condition (2)(a) of Stacks 0GMS on the equi-universe model.** For a quasi-compact
algebraic space there is a finite family of affine objects of the model for which
`∐_j h_{U_j}^# ⟶ *` is a surjection of sheaves of sets. -/
theorem SmallEtaleModel.exists_finite_affineObjects_isLocallySurjective
    (hqc : IsQuasiCompactSpace B S hS F) :
    ∃ (ι : Type u) (_ : Finite ι) (U : ι → SmallEtaleModel B S hS F),
      (∀ i, U i ∈ SmallEtaleModel.affineObjects B S hS F) ∧
        Sheaf.IsLocallySurjective (terminal.from
          (∐ fun i => (Sheaf.sheafifiedYoneda (smallEtaleModelTopology B S hS F)).obj (U i))) := by
  obtain ⟨U, hUaff, hcov⟩ := SmallEtale.exists_affineObject_coversTop B S hS F hF hqc
  refine ⟨PUnit.{u + 1}, inferInstance,
    fun _ => (smallEtaleModelEquivalence B S hS F).inverse.obj U, fun _ => ?_, ?_⟩
  · exact mem_affineObjects_inverse_obj_aux B S hS F hUaff
  · exact Sheaf.isLocallySurjective_terminal_from_sigma_sheafifiedYoneda _ _
      (GrothendieckTopology.coversTop_punit
        (GrothendieckTopology.coversTop_inverse_obj (smallEtaleModelEquivalence B S hS F) hcov))

omit hF in
/-- The image under the inverse of the model equivalence of an affine object of the small étale
site is an affine object of the model. -/
theorem SmallEtaleModel.mem_affineObjects_inverse_obj {U : SmallEtale B S hS F}
    (hU : U ∈ SmallEtale.affineObjects B S hS F) :
    (smallEtaleModelEquivalence B S hS F).inverse.obj U ∈
      SmallEtaleModel.affineObjects B S hS F :=
  mem_affineObjects_inverse_obj_aux B S hS F hU

omit hF in
/-- **Condition (2)(b) of Stacks 0GMS on the equi-universe model.** Every covering of an affine
object of the model is refined by a finite covering by affine objects of the model. -/
theorem SmallEtaleModel.exists_finite_affine_hypercover_hom
    (U : SmallEtaleModel B S hS F) (hU : U ∈ SmallEtaleModel.affineObjects B S hS F)
    (𝒰 : PreZeroHypercover.{u} U)
    (h𝒰 : 𝒰.sieve₀ ∈ smallEtaleModelTopology B S hS F U) :
    ∃ (𝒱 : PreZeroHypercover.{u} U) (_ : 𝒱.Hom 𝒰),
      𝒱.sieve₀ ∈ smallEtaleModelTopology B S hS F U ∧ Finite 𝒱.I₀ ∧
        ∀ i, 𝒱.X i ∈ SmallEtaleModel.affineObjects B S hS F := by
  classical
  have hpush : (𝒰.sieve₀).functorPushforward (smallEtaleModelEquivalence B S hS F).functor ∈
      SmallEtale.topology B S hS F
        ((smallEtaleModelEquivalence B S hS F).functor.obj U) :=
    ((smallEtaleModelEquivalence B S hS F).functor.functorPushforward_mem_iff
      (smallEtaleModelTopology B S hS F) (SmallEtale.topology B S hS F)).2 h𝒰
  obtain ⟨ι, hfin, V, f, hVaff, hle, hcov⟩ :=
    SmallEtale.exists_finite_affine_refinement B S hS F
      ((smallEtaleModelEquivalence B S hS F).functor.obj U) hU _ hpush
  set V' : ι → SmallEtaleModel B S hS F :=
    fun i => (smallEtaleModelEquivalence B S hS F).inverse.obj (V i) with hV'
  set f' : ∀ i, V' i ⟶ U := fun i => (smallEtaleModelEquivalence B S hS F).inverse.map (f i) ≫
    (smallEtaleModelEquivalence B S hS F).unitIso.inv.app U with hf'
  have hcov' : Sieve.ofArrows V' f' ∈ smallEtaleModelTopology B S hS F U :=
    Sieve.ofArrows_inverse_mem (smallEtaleModelEquivalence B S hS F) f hcov
  have hle' : Sieve.ofArrows V' f' ≤ 𝒰.sieve₀ :=
    Sieve.ofArrows_inverse_le (smallEtaleModelEquivalence B S hS F) f hle
  have hVaff' : ∀ i, V' i ∈ SmallEtaleModel.affineObjects B S hS F := fun i =>
    SmallEtaleModel.mem_affineObjects_inverse_obj B S hS F (hVaff i)
  have key : ∀ k : ι, ∃ (j : 𝒰.I₀) (h : V' k ⟶ 𝒰.X j), h ≫ 𝒰.f j = f' k := by
    intro k
    obtain ⟨Y, g, p, hp, hfac⟩ := hle' _ (Sieve.ofArrows_mk V' f' k)
    obtain ⟨j⟩ := hp
    exact ⟨j, g, hfac⟩
  choose jj hh hw using key
  have hpre : Presieve.ofArrows (fun i : ULift.{u} ι => V' i.down) (fun i => f' i.down) =
      Presieve.ofArrows V' f' := by
    refine le_antisymm ?_ ?_
    · rintro Y g ⟨i⟩; exact ⟨i.down⟩
    · rintro Y g ⟨i⟩; exact ⟨ULift.up i⟩
  refine ⟨{ I₀ := ULift.{u} ι, X := fun i => V' i.down, f := fun i => f' i.down },
    { s₀ := fun i => jj i.down, h₀ := fun i => hh i.down, w₀ := fun i => hw i.down },
    ?_, inferInstance, fun i => hVaff' i.down⟩
  show Sieve.generate (Presieve.ofArrows _ _) ∈ _
  rw [hpre]
  exact hcov'

/-! ### Condition (2)(c): the product of two affine objects is covered by one affine object -/

omit hF in
/-- For an object `Q` of the small étale site whose underlying scheme is quasi-compact, there is
an *affine* object `W` of the small étale site and a morphism `W ⟶ Q` whose one-element family is
covering. -/
theorem SmallEtale.exists_affineObject_singleton_mem_precoverage (Q : SmallEtale B S hS F)
    (hQ : CompactSpace ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj Q))) :
    ∃ (W : SmallEtale B S hS F) (p : W ⟶ Q),
      W ∈ SmallEtale.affineObjects B S hS F ∧
        Presieve.singleton p ∈ SmallEtale.precoverage B S hS F Q := by
  set T : BigFppfOver B S hS := (SmallEtale.toOver B S hS F).obj Q with hT
  obtain ⟨W₀, a, hW₀aff, hasurj, haet⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS (yoneda.obj T)
      (isAlgebraicSpace_yoneda B S hS T)).mp (isQuasiCompactSpace_yoneda_obj B S hS hQ)
  set p₀ : W₀ ⟶ T := yoneda.preimage a with hp₀def
  have hp₀ : yoneda.map p₀ = a := yoneda.map_preimage a
  have haet' := presheaf_etale_of_isEtale B S hS haet
  have hetale : Etale ((BigFppfOver.toScheme B S hS).map p₀) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@Etale.{u} : MorphismProperty Scheme.{u}) p₀).1 (by rw [hp₀]; exact haet')
  have hsurj : Surjective ((BigFppfOver.toScheme B S hS).map p₀) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@Surjective.{u} : MorphismProperty Scheme.{u}) p₀).1 (by rw [hp₀]; exact hasurj)
  refine ⟨⟨CostructuredArrow.mk (yoneda.map p₀ ≫ Q.obj.hom),
      etale_comp_of_scheme B S hS p₀ Q.obj.hom hetale Q.property⟩,
    ObjectProperty.homMk (CostructuredArrow.homMk p₀ rfl), hW₀aff, ?_⟩
  rw [SmallEtale.precoverage_eq_comap, Precoverage.mem_comap_iff, Presieve.map_singleton]
  exact B.singleton_mem_etalePrecoverage _ hsurj hetale

variable (hZ : B.Contains (⊤_ Scheme.{u}))

omit hF in
/-- **The product of two quasi-compact objects of the small étale site of a quasi-separated
algebraic space is quasi-compact.** This is Stacks 073B on charts. -/
theorem SmallEtale.compactSpace_prod (hqs : IsAbsolutelyQuasiSeparated B S hS hZ F)
    (U V : SmallEtale B S hS F)
    (hU : CompactSpace ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj U)))
    (hV : CompactSpace ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj V))) :
    CompactSpace ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj (U ⨯ V))) := by
  have hprod : CompactSpace ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj (SmallEtale.prodObj B S hS F U V))) :=
    compactSpace_of_isAbsolutelyQuasiSeparated B S hS hZ hqs
      (U.property.rep.isPullback' V.obj.hom) hU hV
  refine Stacks.Spaces.compactSpace_of_iso ((SmallEtale.toOver B S hS F ⋙
    BigFppfOver.toScheme B S hS).mapIso
      (IsLimit.conePointUniqueUpToIso (SmallEtale.prodIsLimit B S hS F U V)
        (limit.isLimit (pair U V)))) hprod

/-- The model of the small étale site has binary products, being equivalent to a category that
has them. -/
instance hasBinaryProducts_smallEtaleModel : HasBinaryProducts (SmallEtaleModel B S hS F) :=
  Adjunction.hasLimitsOfShape_of_equivalence
    (smallEtaleModelEquivalence B S hS F).functor

omit hF in
/-- **Condition (2)(c) of Stacks 0GMS on the equi-universe model.** For two affine objects of
the model there is a one-element family of affine objects of the model, with morphisms to each,
whose sheafified representable surjects onto the product of their sheafified representables. -/
theorem SmallEtaleModel.exists_finite_affineObjects_isLocallySurjective_prod
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ F)
    (U U' : SmallEtaleModel B S hS F)
    (hU : U ∈ SmallEtaleModel.affineObjects B S hS F)
    (hU' : U' ∈ SmallEtaleModel.affineObjects B S hS F) :
    ∃ (ι : Type u) (_ : Finite ι) (V : ι → SmallEtaleModel B S hS F)
      (a : ∀ i, V i ⟶ U) (b : ∀ i, V i ⟶ U'),
      (∀ i, V i ∈ SmallEtaleModel.affineObjects B S hS F) ∧
        Sheaf.IsLocallySurjective (Limits.Sigma.desc fun i =>
          Limits.prod.lift
            ((Sheaf.sheafifiedYoneda (smallEtaleModelTopology B S hS F)).map (a i))
            ((Sheaf.sheafifiedYoneda (smallEtaleModelTopology B S hS F)).map (b i))) := by
  set e := smallEtaleModelEquivalence B S hS F with he
  have hcompU : CompactSpace ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj (e.functor.obj U))) :=
    have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj (e.functor.obj U))) := hU
    inferInstance
  have hcompU' : CompactSpace ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj (e.functor.obj U'))) :=
    have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj (e.functor.obj U'))) := hU'
    inferInstance
  set κ : e.functor.obj (U ⨯ U') ≅ e.functor.obj U ⨯ e.functor.obj U' :=
    PreservesLimitPair.iso e.functor U U' with hκ
  have hcomp : CompactSpace ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj (e.functor.obj (U ⨯ U')))) :=
    Stacks.Spaces.compactSpace_of_iso ((SmallEtale.toOver B S hS F ⋙
      BigFppfOver.toScheme B S hS).mapIso κ.symm)
      (SmallEtale.compactSpace_prod B S hS F hZ hqs _ _ hcompU hcompU')
  obtain ⟨W, p, hWaff, hpre⟩ :=
    SmallEtale.exists_affineObject_singleton_mem_precoverage B S hS F
      (e.functor.obj (U ⨯ U')) hcomp
  have hcov : Sieve.ofArrows (fun _ : PUnit.{u + 1} => W) (fun _ => p) ∈
      SmallEtale.topology B S hS F (e.functor.obj (U ⨯ U')) := by
    refine (SmallEtale.topology B S hS F).superset_covering ?_
      (Precoverage.generate_mem_toGrothendieck hpre)
    rintro Z f ⟨T, h, k, hk, rfl⟩
    cases hk
    exact ⟨W, h, p, ⟨PUnit.unit⟩, rfl⟩
  have hcov' : Sieve.ofArrows (fun _ : PUnit.{u + 1} => e.inverse.obj W)
      (fun _ => e.inverse.map p ≫ e.unitIso.inv.app (U ⨯ U')) ∈
      smallEtaleModelTopology B S hS F (U ⨯ U') :=
    Sieve.ofArrows_inverse_mem e (fun _ : PUnit.{u + 1} => p) hcov
  set q : e.inverse.obj W ⟶ U ⨯ U' :=
    e.inverse.map p ≫ e.unitIso.inv.app (U ⨯ U') with hq
  refine ⟨PUnit.{u + 1}, inferInstance, fun _ => e.inverse.obj W,
    fun _ => q ≫ Limits.prod.fst, fun _ => q ≫ Limits.prod.snd,
    fun _ => SmallEtaleModel.mem_affineObjects_inverse_obj B S hS F hWaff, ?_⟩
  exact Sheaf.isLocallySurjective_sigmaDesc_prodLift_of_mem _ q hcov'

/-! ### Stacks 07U7 -/

include hF in
/-- The hypothesis of Stacks 0GMR part (4) for the equi-universe model of the small étale
ringed site of a quasi-compact and quasi-separated algebraic space, with the covering set taken
to be the finite coproducts of sheafified representables of affine objects. -/
theorem SmallEtaleModel.exists_set_isLocallySurjective_and_isQuasiCompact_prod_self
    (hqc : IsQuasiCompactSpace B S hS F) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ F) :
    ∃ T : Set (Sheaf (smallEtaleModelTopology B S hS F) (Type u)),
      (∀ H : Sheaf (smallEtaleModelTopology B S hS F) (Type u),
          Sheaf.IsLocallySurjective (terminal.from H) →
            ∃ L ∈ T, Nonempty (L ⟶ H) ∧ Sheaf.IsLocallySurjective (terminal.from L)) ∧
        ∀ L ∈ T, Sheaf.IsQuasiCompact (L ⨯ L) :=
  Sheaf.exists_set_isLocallySurjective_and_isQuasiCompact_prod_self
    (B := SmallEtaleModel.affineObjects B S hS F)
    (SmallEtaleModel.exists_finite_affineObjects_isLocallySurjective B S hS F hF hqc)
    (fun U hU 𝒰 h𝒰 =>
      SmallEtaleModel.exists_finite_affine_hypercover_hom B S hS F U hU 𝒰 h𝒰)
    (fun U hU U' hU' =>
      SmallEtaleModel.exists_finite_affineObjects_isLocallySurjective_prod
        B S hS F hZ hqs U U' hU hU')

include hF in
/-- Let `X` be a quasi-compact and quasi-separated algebraic space over a scheme `S`, let `G` be
an `𝒪_X`-module of finite presentation and let `λ ↦ F_λ` be a filtered system of `𝒪_X`-modules.
Then

`colim_λ Hom_X(G, F_λ) = Hom_X(G, colim_λ F_λ)`,

here in the form that `Hom_X(G, -)` preserves colimits of the given filtered shape, which says
exactly that the canonical comparison map out of any such colimit is a bijection. The module
universe is the universe `u` of the schemes. -/
@[stacks 07U7]
theorem preservesColimitsOfShape_coyoneda_of_isFinitePresentation
    (hqc : IsQuasiCompactSpace B S hS F) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ F)
    (G : Modules.{u, u} B S hS F hF) [G.IsFinitePresentation]
    (K : Type u) [Category.{u} K] [IsFiltered K] :
    PreservesColimitsOfShape K (coyoneda.obj (Opposite.op G)) :=
  preservesColimitsOfShape_coyoneda_of_isFinitePresentation_model B S hS F hF G
    (isFinitePresentation_modulesEquivModelModules B S hS F hF G) K
    (SmallEtaleModel.exists_set_isLocallySurjective_and_isQuasiCompact_prod_self
      B S hS F hF hZ hqc hqs)

end AlgebraicGeometry.Space

end
