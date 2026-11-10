module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.SheafifiedHigherDirectImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CohomologyViaSectionComplex
import StacksCore.Tactic.StacksAttribute

/-!
# The induction step for the vanishing condition under a change of topology

In the situation of Stacks 0EZ3 write `ε_X : C_τ/X ⟶ C_τ'/X` for the change-of-topology
morphism and let `(V_n)` be the condition
`Stacks.ComparingTopologies.CohomologyComparison.vanishingCondition`: the higher direct images
`R^i ε_{X,*} ℱ` vanish for `1 ≤ i ≤ n`, for every object `X` and every `ℱ` of the class `𝒜_X`.

This file reduces **Stacks 0EZE**, the induction step `(V_n) ⇒ (V_{n+1})`, to the descent
statement which the source's proof reaches after its reduction step, recorded here as
`Stacks.ComparingTopologies.CohomologyComparison.SingleCoveringDescent`: for a morphism
`f : W ⟶ V` of the localized site whose underlying arrow lies in the distinguished class and
which by itself is a covering for the finer topology, a class `ζ ∈ H^{m}_τ(V, ℱ)` whose
restriction to `W` dies on a covering of `W` for the coarser topology already dies on a covering
of `V` for the coarser topology.

## The reduction

By Stacks 072W the sheaf `R^{n+1} ε_{X,*} ℱ` is the sheafification, for the coarser topology, of
the presheaf of degree-`n+1` cohomology classes, so it vanishes as soon as every class
`ξ ∈ H^{n+1}_τ(U, ℱ)`, over every object `U` of `C_τ/X`, dies on a covering of `U` for the
coarser topology. Fix such a `ξ` and let `E` be the sieve of morphisms into `U` along which `ξ`
restricts to zero; the claim is that `E` covers `U` for the coarser topology.

Locality of cohomology, Stacks 01FW, gives a covering of `U` for the *finer* topology inside `E`,
and hence a finer covering family `R` of `U.left`. The three-stage refinement assumption of the
situation refines `R` by a coarse covering family `{V_j → U.left}`, a single arrow
`f_j : W_j ⟶ V_j` of the distinguished class which is a fine covering, and a coarse covering
family `{W_{jk} → W_j}` factoring through `R` along `f_j`. Over each `V_j` the class `ξ` restricts
to zero along every `W_{jk}`, because each of those arrows factors through a member of `R`; so the
assumed descent statement applies to `ξ|_{V_j}` and makes it die on a coarse covering of `V_j`.
Transitivity of the coarser topology then puts `E` in it, since `{V_j → U}` is a coarse covering
and `E` pulled back along `V_j ⟶ U` is covering.

The degrees `1, …, n` of `(V_{n+1})` are `(V_n)` itself; `(V_n)` enters degree `n + 1` only
through the assumed descent statement, which is where the source uses Stacks 0EZB, 0EZC and
0EZD.

## Main definitions

* `Stacks.ComparingTopologies.CohomologyComparison.SingleCoveringDescent`: the descent statement
  for a single covering arrow of the distinguished class, in degree `m`.

## Main results

* `Stacks.sheafCohomologyRestriction_comp`: restriction of cohomology classes is functorial.
* `Stacks.exists_cohomologyCover_restrict_eq_zero`: **Stacks 01FW** for cohomology classes — a
  class of positive degree dies on a covering of its domain.
* `Stacks.ComparingTopologies.exists_coarseCover_restrict_eq_zero`: the reduction above, that
  every class of positive degree dies on a covering for the coarser topology.
* `CohomologyComparison.vanishingCondition_succ_of_singleCoveringDescent`:
  Stacks 0EZE granted the descent statement (proved in `SingleCoveringDescent`).

## Implementation notes

Cohomology over an object of a site is `Stacks.sheafCohomology`, the right derived functors of
the sections over that object, and `Stacks.sheafCohomologyRestriction` is the restriction map
between two of them; functoriality of those restrictions is not available from the derived
functors directly and is obtained here from the description of cohomology as the homology of the
complex of sections of an injective resolution.

The covering families of the situation are presieves on objects of `C`, while the cohomology
classes live over objects of the slice category `Over X`; the translation is
`CategoryTheory.Sieve.overEquiv` together with
`CategoryTheory.Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition`, which produces a
covering family inside a covering sieve.

## References

* [Stacks Project, Tag 0EZE](https://stacks.math.columbia.edu/tag/0EZE)
* [Stacks Project, Tag 0EZ3](https://stacks.math.columbia.edu/tag/0EZ3)
* [Stacks Project, Tag 01FW](https://stacks.math.columbia.edu/tag/01FW)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks

/-- The comparison of cohomology with the homology of sections is injective. -/
private lemma sectionHomologyIso_hom_injective {D : Type u} [Category.{v} D]
    (J : GrothendieckTopology D) [HasSheafify J Ab.{max u v}] (F : Sheaf J Ab.{max u v}) (m : ℕ)
    (Z : D) :
    Function.Injective
      (Stacks.Cohomology.Locality.sectionHomologyIso J F (injectiveResolution F) m Z).hom :=
  (AddCommGrpCat.mono_iff_injective _).1 inferInstance

/-- Restriction of cohomology classes is functorial: restricting along a composite is
restricting along the two factors in turn. -/
lemma sheafCohomologyRestriction_comp {D : Type u} [Category.{v} D]
    (J : GrothendieckTopology D) [HasSheafify J Ab.{max u v}] (F : Sheaf J Ab.{max u v}) (m : ℕ)
    {Z Y U : D} (k : Z ⟶ Y) (h : Y ⟶ U) (ξ : sheafCohomology J F U m) :
    sheafCohomologyRestriction J (k ≫ h) m F ξ =
      sheafCohomologyRestriction J k m F (sheafCohomologyRestriction J h m F ξ) := by
  apply sectionHomologyIso_hom_injective J F m Z
  rw [Stacks.Cohomology.Locality.sectionHomologyIso_restrict,
    Stacks.Cohomology.Locality.sectionHomologyIso_restrict,
    Stacks.Cohomology.Locality.sectionHomologyIso_restrict, op_comp, Functor.map_comp,
    ConcreteCategory.comp_apply]

/-- **Stacks 01FW for cohomology classes.** A cohomology class of positive degree over an object
of a site restricts to zero on the members of some covering of that object. -/
lemma exists_cohomologyCover_restrict_eq_zero {D : Type u} [Category.{v} D]
    (J : GrothendieckTopology D) [HasSheafify J Ab.{max u v}] (F : Sheaf J Ab.{max u v}) (m : ℕ)
    (hm : 0 < m)
    (U : D) (ξ : sheafCohomology J F U m) :
    ∃ R : J.Cover U, ∀ g : R.Arrow, sheafCohomologyRestriction J g.f m F ξ = 0 := by
  obtain ⟨R, hR⟩ :=
    Stacks.Cohomology.Locality.injectiveResolution_homology_presheaf_locally_zero F
      (injectiveResolution F) m hm U
      ((Stacks.Cohomology.Locality.sectionHomologyIso J F (injectiveResolution F) m U).hom ξ)
  refine ⟨R, fun g => ?_⟩
  apply sectionHomologyIso_hom_injective J F m g.Y
  rw [map_zero, Stacks.Cohomology.Locality.sectionHomologyIso_restrict]
  exact hR g

namespace ComparingTopologies

variable {C : Type u} [Category.{v} C]

/-- **The descent statement for a single covering arrow of the distinguished class.** For
`f : W ⟶ V` a morphism of the site localized at `X` whose underlying arrow lies in the
distinguished class and which by itself is a covering for the finer topology, and for `ℱ` in
`𝒜_X`, a class of degree `m` over `V` whose restriction to `W` dies on a covering of `W` for the
coarser topology dies on a covering of `V` for the coarser topology.

This is the situation the source's proof of Stacks 0EZE reaches after refining the covering on
which the class dies. -/
def CohomologyComparison.SingleCoveringDescent (S : CohomologyComparison C) (m : ℕ) : Prop :=
  ∀ (X : C) (F : Sheaf (S.fineCoverage.toGrothendieck.over X) Ab.{max u v}), S.fineWeakSerre X F →
    ∀ (V W : Over X) (f : W ⟶ V), S.morphismProperty f.left →
      Presieve.singleton f.left ∈ S.fineCoverage V.left →
        ∀ ζ : Stacks.sheafCohomology (S.fineCoverage.toGrothendieck.over X) F V m,
          (∃ R : (S.coarseCoverage.toGrothendieck.over X).Cover W, ∀ g : R.Arrow,
            Stacks.sheafCohomologyRestriction (S.fineCoverage.toGrothendieck.over X)
              (g.f ≫ f) m F ζ = 0) →
          ∃ R : (S.coarseCoverage.toGrothendieck.over X).Cover V, ∀ g : R.Arrow,
            Stacks.sheafCohomologyRestriction (S.fineCoverage.toGrothendieck.over X)
              g.f m F ζ = 0

/-- **Every cohomology class of positive degree dies on a covering for the coarser topology**,
granted the descent statement for a single covering arrow of the distinguished class.

Locality of cohomology makes the class die on a covering for the finer topology; the three-stage
refinement assumption of the situation refines that covering by a coarse covering, a single
covering arrow of the distinguished class over each member, and a further coarse covering, and
the assumed descent statement disposes of each member of the first stage. -/
theorem exists_coarseCover_restrict_eq_zero (S : CohomologyComparison C) (m : ℕ) (hm : 0 < m)
    (hdesc : S.SingleCoveringDescent m) (X : C)
    (F : Sheaf (S.fineCoverage.toGrothendieck.over X) Ab.{max u v}) (hF : S.fineWeakSerre X F)
    (U : Over X) (ξ : Stacks.sheafCohomology (S.fineCoverage.toGrothendieck.over X) F U m) :
    ∃ R : (S.coarseCoverage.toGrothendieck.over X).Cover U, ∀ g : R.Arrow,
      Stacks.sheafCohomologyRestriction (S.fineCoverage.toGrothendieck.over X) g.f m F ξ = 0 := by
  let Jf := S.fineCoverage.toGrothendieck.over X
  let Jc := S.coarseCoverage.toGrothendieck.over X
  -- the sieve of arrows into `U` along which `ξ` restricts to zero
  let E : Sieve U :=
    { arrows := fun _ h => Stacks.sheafCohomologyRestriction Jf h m F ξ = 0
      downward_closed := by
        intro Y Z h (hh : Stacks.sheafCohomologyRestriction Jf h m F ξ = 0) g
        rw [Stacks.sheafCohomologyRestriction_comp, hh, map_zero] }
  -- `ξ` dies on a covering for the finer topology
  obtain ⟨R₁, hR₁⟩ := Stacks.exists_cohomologyCover_restrict_eq_zero Jf F m hm U ξ
  -- and hence on a fine covering family of `U.left`
  obtain ⟨R₀, hR₀mem, hR₀le⟩ :=
    S.fineCoverage.mem_toGrothendieck_iff_of_isStableUnderComposition.mp
      ((S.fineCoverage.toGrothendieck.mem_over_iff R₁.1).1 R₁.2)
  have hR₀E : ∀ ⦃Y : C⦄ (r : Y ⟶ U.left), R₀ r →
      E (Over.homMk r : Over.mk (r ≫ U.hom) ⟶ U) :=
    fun _ r hr => hR₁ ⟨_, _, (Sieve.overEquiv_iff R₁.1 r).1 (hR₀le _ r hr)⟩
  -- the three-stage refinement of that family
  obtain ⟨T, hTmem, hT⟩ := S.covering_refinement U.left R₀ hR₀mem
  have key : ∀ ⦃V : C⦄ (v : V ⟶ U.left), T v →
      E.pullback (Over.homMk v : Over.mk (v ≫ U.hom) ⟶ U) ∈ Jc (Over.mk (v ≫ U.hom)) := by
    intro V v hv
    obtain ⟨W, f, hPf, hfcov, T', hT'mem, hfact⟩ := hT v hv
    let Vo : Over X := Over.mk (v ≫ U.hom)
    let wv : Vo ⟶ U := Over.homMk v
    let Wo : Over X := Over.mk (f ≫ v ≫ U.hom)
    let fv : Wo ⟶ Vo := Over.homMk f
    -- the restriction of `ξ` to `Vo` dies on the coarse covering `T'` of `Wo`
    have hinput : ∃ R' : Jc.Cover Wo, ∀ g : R'.Arrow,
        Stacks.sheafCohomologyRestriction Jf (g.f ≫ fv) m F
          (Stacks.sheafCohomologyRestriction Jf wv m F ξ) = 0 := by
      refine ⟨⟨(Sieve.overEquiv Wo).symm (Sieve.generate T'),
        S.coarseCoverage.toGrothendieck.overEquiv_symm_mem_over Wo _
          (S.coarseCoverage.generate_mem_toGrothendieck hT'mem)⟩, fun g => ?_⟩
      obtain ⟨Y₁, b, t, hTt, hbt⟩ : Sieve.generate T' g.f.left := g.hf
      obtain ⟨W₂, i, e, hR₀e, hie⟩ := hfact hTt
      have hwg : g.f.left ≫ f ≫ v ≫ U.hom = g.Y.hom := Over.w g.f
      have h1 : b ≫ i ≫ e = g.f.left ≫ f ≫ v := by
        rw [hie, ← hbt]
        simp
      have hbie : (b ≫ i) ≫ (Over.mk (e ≫ U.hom) : Over X).hom = g.Y.hom :=
        calc (b ≫ i) ≫ (Over.mk (e ≫ U.hom) : Over X).hom
            = (b ≫ i ≫ e) ≫ U.hom := by simp
          _ = (g.f.left ≫ f ≫ v) ≫ U.hom := by rw [h1]
          _ = g.Y.hom := by rw [← hwg]; simp
      have hfac : (g.f ≫ fv) ≫ wv =
          (Over.homMk (b ≫ i) hbie : g.Y ⟶ Over.mk (e ≫ U.hom)) ≫
            (Over.homMk e : Over.mk (e ≫ U.hom) ⟶ U) := by
        ext
        change (g.f.left ≫ f) ≫ v = (b ≫ i) ≫ e
        rw [Category.assoc, ← h1]
        simp
      rw [← Stacks.sheafCohomologyRestriction_comp]
      have hmem : E ((g.f ≫ fv) ≫ wv) := by
        rw [hfac]
        exact E.downward_closed (hR₀E e hR₀e) _
      exact hmem
    obtain ⟨R'', hR''⟩ := hdesc X F hF Vo Wo fv hPf hfcov
      (Stacks.sheafCohomologyRestriction Jf wv m F ξ) hinput
    refine Jc.superset_covering ?_ R''.2
    intro Z h hh
    change Stacks.sheafCohomologyRestriction Jf (h ≫ wv) m F ξ = 0
    rw [Stacks.sheafCohomologyRestriction_comp]
    exact hR'' ⟨Z, h, hh⟩
  -- transitivity of the coarser topology along the first stage of the refinement
  have hEmem : E ∈ Jc U := by
    refine Jc.transitive (S.coarseCoverage.toGrothendieck.overEquiv_symm_mem_over U _
      (S.coarseCoverage.generate_mem_toGrothendieck hTmem)) E ?_
    intro Z w hw
    obtain ⟨Y₀, a, v, hTv, hav⟩ : Sieve.generate T w.left := hw
    have hav' : a ≫ (Over.mk (v ≫ U.hom) : Over X).hom = Z.hom := by
      change a ≫ v ≫ U.hom = Z.hom
      rw [← Category.assoc, hav]
      exact Over.w w
    have hfacw : (Over.homMk a hav' : Z ⟶ Over.mk (v ≫ U.hom)) ≫
        (Over.homMk v : Over.mk (v ≫ U.hom) ⟶ U) = w := by
      ext
      change a ≫ v = w.left
      exact hav
    rw [← hfacw, Sieve.pullback_comp]
    exact Jc.pullback_stable _ (key v hTv)
  exact ⟨⟨E, hEmem⟩, fun g => g.hf⟩

/-- **The induction step of Stacks 0EZE, from the descent statement.** In the comparison situation
of Stacks 0EZ3 the vanishing condition `(V_n)` implies `(V_{n+1})`, granted the descent statement
`Stacks.ComparingTopologies.CohomologyComparison.SingleCoveringDescent` in degree `n + 1`.

The degrees `1, …, n` are `(V_n)` itself. Degree `n + 1` is the vanishing criterion of
Stacks 072W fed with `Stacks.ComparingTopologies.exists_coarseCover_restrict_eq_zero`. -/
theorem CohomologyComparison.vanishingCondition_succ_of_singleCoveringDescent
    (S : CohomologyComparison C) (n : ℕ)
    (hV : S.vanishingCondition n) (hdesc : S.SingleCoveringDescent (n + 1)) :
    S.vanishingCondition (n + 1) := by
  intro X F hF i hi1 hi2
  rcases Nat.lt_or_ge i (n + 1) with h | h
  · exact hV X F hF i hi1 (by omega)
  · obtain rfl : i = n + 1 := by omega
    exact isZero_rightDerived_abelianComparisonPushforward_of_locally_zero' S X F (n + 1)
      (exists_coarseCover_restrict_eq_zero S (n + 1) n.succ_pos hdesc X F hF)

end ComparingTopologies

end Stacks

end
