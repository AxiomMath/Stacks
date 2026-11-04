module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationFromQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientAlgebraic
public import StacksFrontier.AlgebraicGeometry.Stacks.StructureSheaf
public import StacksFrontier.CategoryTheory.Sites.Sheafification.SurjectionCoequalizer

/-!
# An étale sheaf with an étale presentation is an algebraic space

Let `S` be a scheme contained in a chosen big fppf site `B`. A presheaf of sets on the big fppf
category over `S` which is a sheaf for the chosen *étale* topology, whose diagonal is
representable and which admits a surjective étale atlas by a scheme is an algebraic space over
`S` — the only thing to prove is that it is a sheaf for the *fppf* topology.

The mechanism is a comparison of two quotients. The atlas `f : h_U ⟶ F` is surjective for the
étale topology, and its kernel pair is the represented presheaf of an étale equivalence relation
`R` on `U`; so `F` is the coequalizer of `h_R ⇉ h_U` in étale sheaves. The fppf quotient sheaf
`U/R` of the same relation has the *same* kernel pair and is likewise an étale-local quotient of
`h_U`, so it is the same coequalizer, and `F` inherits the fppf sheaf condition from it.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.generate_singleton_mem_etaleTopology`: a one-element family of the
  common underlying category whose morphism of schemes is surjective and étale generates a
  covering sieve of the chosen étale topology.
* `AlgebraicGeometry.Space.exists_etaleCover_lift_of_surjective_etale`: a surjective étale
  morphism of the big fppf category over `S` admits local sections on a covering sieve of the
  chosen étale topology.
* `AlgebraicGeometry.Space.isLocallySurjective_etaleTopology_of_presheaf`: a morphism from a
  represented presheaf which is surjective and étale after every representable base change is
  locally surjective for the chosen étale topology. This is the étale-sheaf form of the
  surjectivity of an atlas, and it is independent of any fppf descent.
* `AlgebraicGeometry.Space.isAlgebraicSpace_of_isSheaf_etale_of_isLocallySurjective_quotientMap`:
  **Stacks 076M** granted that sections of the fppf quotient sheaf lift étale-locally.
* `AlgebraicGeometry.Space.isAlgebraicSpace_of_isSheaf_etale_of_isAlgebraicSpace_quotientSheaf`:
  the same conclusion from the full statement of Stacks 02WW.

## Implementation notes

**What this file does not discharge.** The comparison needs the fppf quotient sheaf `U/R` of an
étale equivalence relation to be an étale-local quotient of `h_U`: every section of `U/R` must
lift to a point of `U` on a covering sieve of the *étale* topology. That single statement is
the whole residue, and it is what the main theorem carries as a hypothesis; granted it, the
rest of the argument is unconditional, the kernel-pair clause
`AlgebraicGeometry.Space.quotientMap_isPullback` included.

The residue is not merely hard, it is a theorem of flat descent. A section of `U/R` over `T`
lifts *fppf*-locally by construction; an étale-local lift is a scheme `T ×_{U/R} U`, étale and
surjective over `T`, obtained by descending the étale scheme `T' ×_{U/R} U` along the fppf
covering `T' → T` on which the section is represented. Effectivity of fppf descent data for
étale schemes is Stacks 0247, which rests on Gabber's Stacks 0APK, which in this library
needs three further developments (Stacks 02W3, 0APF, 0AP4). There is no cheaper route: an
étale sheaf need not be an fppf sheaf — the two topologies differ exactly on inseparable
covers — so the extra content has to come from descent, and the atlas hypotheses alone give it
only along étale coverings. For that reason the main theorem does **not** carry
`@[stacks 076M]`: its statement is weaker than the source, which proves the result outright.

The three auxiliary results above are unconditional and stated so as to be usable on their
own; in particular `isLocallySurjective_etaleTopology_of_presheaf` discharges, for `F` itself,
the clause that remains open for `U/R`.

**`hquot` is now dischargeable, and the tag lives elsewhere.** The reasoning recorded in the
two paragraphs above describes the state of this development when the file was written, when
Stacks 02WW was available here only under an effective-descent hypothesis. It is no longer the
state: `AlgebraicGeometry.Space.quotientMap_surjective_unconditional` and
`AlgebraicGeometry.Space.quotientMap_etale_unconditional` of
`StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional` prove 02WW's two
chart clauses assuming only that the relation is an étale equivalence relation, and composing
them with `isLocallySurjective_etaleTopology_of_presheaf` produces `hquot` outright — so the
route through flat descent described above, Stacks 0247 and Gabber's Stacks 0APK, is not the
only one and is not the one taken. Accordingly
`StacksFrontier.AlgebraicGeometry.Spaces.EtaleSheafAlgebraicCriterionTag076M` states Stacks 076M
with the source's three hypotheses and nothing more, and it is
`AlgebraicGeometry.Space.isAlgebraicSpace_of_isSheaf_etale` there that carries
`@[stacks 076M]`. The two theorems below keep their hypotheses and stay untagged: each is still
weaker than the source, and they remain the reusable comparison the tagged form is built on.

**Universes.** The coequalizer criterion for a surjection of sheaves of sets,
`CategoryTheory.coequalizer_of_surjection`, is stated at the universe `max v u` of a site with
objects in `Type u` and morphisms in `Type v`; the big fppf category over `S` has objects in
`Type (u + 1)` and morphisms in `Type u`, so the comparison is carried out after composing the
presheaves with `CategoryTheory.uliftFunctor`, and the fppf sheaf condition is transported back
along `CategoryTheory.Presheaf.isSheaf_of_isSheaf_comp`.

## References

* [Stacks Project, Tag 076M](https://stacks.math.columbia.edu/tag/076M)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 0247](https://stacks.math.columbia.edu/tag/0247)
* [Stacks Project, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK)
* [Stacks Project, Tag 086K](https://stacks.math.columbia.edu/tag/086K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Groupoids

universe u

namespace AlgebraicGeometry.Space

/-! ### Étale-local surjectivity of an atlas -/

/-- A one-element family of the common underlying category of the chosen big fppf and étale
sites whose morphism of schemes is surjective and étale generates a covering sieve of the chosen
étale topology. -/
theorem generate_singleton_mem_etaleTopology (B : BigFppfSite.{u}) {X Y : B.Schemes}
    (g : Y ⟶ X) (hs : Surjective (B.inclusion.map g)) (he : Etale (B.inclusion.map g)) :
    Sieve.generate (Presieve.singleton g) ∈ etaleTopology B X := by
  have hEt : Presieve.singleton (B.inclusion.map g) ∈
      Scheme.etalePrecoverage (B.inclusion.obj X) := by
    have : Surjective (B.inclusion.map g) := hs
    exact (Scheme.singleton_mem_precoverage_iff (@Etale.{u} : MorphismProperty Scheme.{u})
      (B.inclusion.map g)).2 ⟨Scheme.Hom.surjective (B.inclusion.map g), he⟩
  have hE : IsEtaleCovering (⟨X, PreZeroHypercover.singleton g⟩ : Covering B.Schemes) := by
    show ((PreZeroHypercover.singleton g).map B.inclusion).presieve₀ ∈
      Scheme.etalePrecoverage (B.inclusion.obj X)
    rw [PreZeroHypercover.presieve₀_map, PreZeroHypercover.presieve₀_singleton,
      Presieve.map_singleton]
    exact hEt
  obtain ⟨E', hE', hX, hComb⟩ := etaleCovering_has_representative B _ hE
  have hpre : (PreZeroHypercover.singleton g).presieve₀ ∈ etalePrecoverage B X := by
    cases hX
    rw [PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hComb]
    exact ⟨E'.2, rfl, hE'⟩
  simpa only [PreZeroHypercover.presieve₀_singleton] using
    Precoverage.generate_mem_toGrothendieck hpre

/-- A morphism of the big fppf category over `S` whose morphism of schemes is surjective and
étale admits a section on every arrow of a covering sieve of the chosen étale topology. -/
theorem exists_etaleCover_lift_of_surjective_etale (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {P T : BigFppfOver B S hS} (q : P ⟶ T)
    (hs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (he : Etale ((BigFppfOver.toScheme B S hS).map q)) :
    ∃ Z : Sieve T, Z ∈ (etaleTopology B).over (B.obj hS) T ∧
      ∀ ⦃W : BigFppfOver B S hS⦄ (k : W ⟶ T), Z k → ∃ a : W ⟶ P, a ≫ q = k := by
  have hbase : Sieve.generate (Presieve.singleton ((BigFppfOver.forget B S hS).map q)) ∈
      etaleTopology B T.left :=
    generate_singleton_mem_etaleTopology B _ hs he
  refine ⟨(Sieve.overEquiv T).symm
    (Sieve.generate (Presieve.singleton ((BigFppfOver.forget B S hS).map q))),
    (etaleTopology B).overEquiv_symm_mem_over T _ hbase, ?_⟩
  intro W k hk
  have hk₀ : Sieve.generate (Presieve.singleton ((BigFppfOver.forget B S hS).map q)) k.left := by
    simpa using hk
  obtain ⟨V, a₀, b₀, hb₀, hfac₀⟩ := hk₀
  cases hb₀
  refine ⟨Over.homMk a₀ ?_, ?_⟩
  · calc
      a₀ ≫ P.hom = a₀ ≫ q.left ≫ T.hom := by rw [← Over.w q]
      _ = (a₀ ≫ (BigFppfOver.forget B S hS).map q) ≫ T.hom := by
        rw [← Category.assoc]; rfl
      _ = k.left ≫ T.hom := by rw [hfac₀]
      _ = W.hom := Over.w k
  · exact Over.OverMorphism.ext hfac₀

/-- **A surjective étale atlas is locally surjective for the étale topology.** A morphism from a
represented presheaf on the big fppf category over `S` which is surjective and étale after every
representable base change is locally surjective for the chosen étale topology: every section of
the target lifts, on a covering sieve of the étale topology, to a point of the representing
object. -/
theorem isLocallySurjective_etaleTopology_of_presheaf (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U : BigFppfOver B S hS}
    (g : yoneda.obj U ⟶ Y)
    (hsurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g)
    (hetale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g) :
    Presheaf.IsLocallySurjective ((etaleTopology B).over (B.obj hS)) g := by
  refine ⟨fun {T} ξ ↦ ?_⟩
  set h : yoneda.obj T ⟶ Y := yonedaEquiv.symm ξ with hh
  have hrep : yoneda.relativelyRepresentable g := hsurj.rep
  have hpb := hrep.isPullback h
  obtain ⟨Z, hZ, hlift⟩ := exists_etaleCover_lift_of_surjective_etale B S hS (hrep.snd h)
    (hsurj.property h (hrep.fst h) (hrep.snd h) hpb)
    (hetale.property h (hrep.fst h) (hrep.snd h) hpb)
  refine ((etaleTopology B).over (B.obj hS)).superset_covering ?_ hZ
  intro W k hk
  obtain ⟨a, hak⟩ := hlift k hk
  refine ⟨yonedaEquiv (yoneda.map a ≫ hrep.fst h), ?_⟩
  rw [← yonedaEquiv_comp]
  have hξ : ξ = yonedaEquiv h := by rw [hh]; simp
  rw [hξ, yonedaEquiv_naturality]
  refine congrArg yonedaEquiv ?_
  calc
    (yoneda.map a ≫ hrep.fst h) ≫ g = yoneda.map a ≫ hrep.fst h ≫ g := Category.assoc _ _ _
    _ = yoneda.map a ≫ yoneda.map (hrep.snd h) ≫ h := by rw [hpb.w]
    _ = yoneda.map (a ≫ hrep.snd h) ≫ h := by rw [Functor.map_comp, Category.assoc]
    _ = yoneda.map k ≫ h := by rw [hak]

/-! ### The comparison with the fppf quotient sheaf -/

/-- Two points of `U` which a map `g` out of `h_U` with kernel pair `R` identifies are identified
by every map out of `h_U` which coequalizes the two projections of `R`. -/
private theorem app_eq_of_app_eq_of_isPullback {C : Type*} [Category.{u} C]
    {Y Z : Cᵒᵖ ⥤ Type u} {R U : C} {t s : R ⟶ U} {g : yoneda.obj U ⟶ Y} {h : yoneda.obj U ⟶ Z}
    (hg : IsPullback (yoneda.map t) (yoneda.map s) g g)
    (hh : yoneda.map t ≫ h = yoneda.map s ≫ h)
    {V : C} {x y : V ⟶ U} (hxy : g.app (op V) x = g.app (op V) y) :
    h.app (op V) x = h.app (op V) y := by
  have hx : yoneda.map x ≫ g = yoneda.map y ≫ g := yonedaEquiv.injective <| by
    rwa [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_yoneda_map]
  have hcomp : yoneda.map x ≫ h = yoneda.map y ≫ h := by
    rw [← hg.lift_fst _ _ hx, Category.assoc, hh, ← Category.assoc, hg.lift_snd]
  have := congrArg yonedaEquiv hcomp
  rwa [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_yoneda_map] at this

open Stacks.Sites.SurjectionCoequalizer in
/-- **Stacks 076M, granted the étale-local surjectivity of the fppf quotient map.** A presheaf
of sets on the big fppf category over `S` which is a sheaf for the chosen étale topology, whose
diagonal is representable and which admits a surjective étale atlas by a scheme is an algebraic
space over `S`.

The hypothesis `hquot` says that a section of the fppf quotient sheaf of an étale equivalence
relation lifts, on a covering sieve of the *étale* topology, to a point of the presenting
object. It is the single residue of Stacks 02WW left by this proof, and it is exactly the
statement that fppf descent data of étale schemes are effective: a section of `U/R` over `T`
lifts fppf-locally by construction, and asking for an étale-local lift asks for the étale
`T`-scheme `T ×_{U/R} U` to exist. That is Stacks 0247, which rests on Gabber's Stacks 0APK.

Granted `hquot`, nothing else of 02WW is needed: the kernel-pair clause
`AlgebraicGeometry.Space.quotientMap_isPullback` holds unconditionally, and the surjective and
étale clauses enter only by producing `hquot` itself.

This theorem does **not** carry `@[stacks 076M]`, and must not. Stacks 076M's source *proves*
the result, citing Stacks 02WW as an established theorem; hypothesising 02WW's conclusion makes
this statement strictly weaker than its source, and a tag may not be certified by a statement
weaker than the source it names. (For the same reason `hasCoproducts_quasicoherentDerivedCategory`, which assumes as a
hypothesis a clause of Stacks 03M1 that its own source proves, does not carry
`@[stacks 08F3]`.) -/
theorem isAlgebraicSpace_of_isSheaf_etale_of_isLocallySurjective_quotientMap
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : Presheaf.IsSheaf ((etaleTopology B).over (B.obj hS)) F)
    (hdiag : yoneda.relativelyRepresentable (diag F))
    (hatlas : ∃ (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ F),
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf f ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf f)
    (hquot : ∀ {R U : BigFppfOver B S hS} (s t : R ⟶ U),
      IsEtaleEquivalenceRelation (relation B S hS s t) →
        Presheaf.IsLocallySurjective ((etaleTopology B).over (B.obj hS))
          (quotientMap B S hS s t)) :
    IsAlgebraicSpace B S hS F := by
  classical
  obtain ⟨U, f, hsurj, hetale⟩ := hatlas
  -- `R` is the kernel pair of the atlas, and the two projections form an étale equivalence
  -- relation on `U` over `S`.
  have hrep : yoneda.relativelyRepresentable f := hsurj.rep
  set R : BigFppfOver B S hS := hrep.pullback f with hR
  set source : R ⟶ U := hrep.snd f with hsrc
  set target : R ⟶ U := yoneda.preimage (hrep.fst f) with htgt
  have hpull : IsPullback (yoneda.map target) (yoneda.map source) f f := by
    simpa only [htgt, Functor.map_preimage] using hrep.isPullback f
  have hEtaleTarget : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) target :=
    hetale.property f (yoneda.map source) target hpull.flip
  have hEtaleSource : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) source :=
    hetale.property f (yoneda.map target) source hpull
  have htargetJ : (relation B S hS source target).target =
      (Over.post B.inclusion).map target :=
    prod.lift_fst _ _
  have hsourceJ : (relation B S hS source target).source =
      (Over.post B.inclusion).map source :=
    prod.lift_snd _ _
  have : IsEquivalenceRelation (relation B S hS source target).target
      (relation B S hS source target).source := by
    rw [htargetJ, hsourceJ]
    exact isEquivalenceRelation_of_isPullback B S hS f target source hpull
  have : Etale (relation B S hS source target).source.left := by
    rw [hsourceJ]; exact hEtaleSource
  have : Etale (relation B S hS source target).target.left := by
    rw [htargetJ]; exact hEtaleTarget
  have hjEt : IsEtaleEquivalenceRelation (relation B S hS source target) := ⟨⟩
  -- The fppf quotient sheaf of the relation, and its canonical map.
  set Q := quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
    (relation B S hS source target) with hQdef
  set q : yoneda.obj U ⟶ Q.obj := quotientMap B S hS source target with hq
  have hqpull : IsPullback (yoneda.map target) (yoneda.map source) q q :=
    quotientMap_isPullback B S hS source target
  -- Both maps out of `h_U` are locally surjective for the étale topology.
  have hlocF : Presheaf.IsLocallySurjective ((etaleTopology B).over (B.obj hS)) f :=
    isLocallySurjective_etaleTopology_of_presheaf B S hS f hsurj hetale
  have hlocQ : Presheaf.IsLocallySurjective ((etaleTopology B).over (B.obj hS)) q :=
    hquot source target hjEt
  -- The étale topology is coarser than the fppf topology, so `h_U` and `Q` are étale sheaves.
  have hle : (etaleTopology B).over (B.obj hS) ≤ BigFppfOver.topology B S hS := by
    intro X Z hZ
    rw [GrothendieckTopology.mem_over_iff] at hZ ⊢
    exact Stack.etaleTopology_le_topology B X.left hZ
  have : (BigFppfOver.topology B S hS).Subcanonical := by
    show (B.topology.over (B.obj hS)).Subcanonical
    have : B.topology.Subcanonical := BigFppfSite.subcanonical_topology B
    infer_instance
  have hUfppf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (yoneda.obj U) :=
    (isSheaf_iff_isSheaf_of_type _ _).mpr
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
        (J := BigFppfOver.topology B S hS) (yoneda.obj U))
  have hUeta := Presheaf.IsSheaf.of_le hle hUfppf
  have hQeta := Presheaf.IsSheaf.of_le hle Q.property
  -- Pass to the universe in which the coequalizer criterion is stated.
  have hUL : Presheaf.IsSheaf ((etaleTopology B).over (B.obj hS))
      (yoneda.obj U ⋙ uliftFunctor.{u + 1}) :=
    Presheaf.isSheaf_comp_of_isSheaf _ _ uliftFunctor.{u + 1} hUeta
  have hFL : Presheaf.IsSheaf ((etaleTopology B).over (B.obj hS))
      (F ⋙ uliftFunctor.{u + 1}) :=
    Presheaf.isSheaf_comp_of_isSheaf _ _ uliftFunctor.{u + 1} hF
  have hQL : Presheaf.IsSheaf ((etaleTopology B).over (B.obj hS))
      (Q.obj ⋙ uliftFunctor.{u + 1}) :=
    Presheaf.isSheaf_comp_of_isSheaf _ _ uliftFunctor.{u + 1} hQeta
  set UF : Sheaf ((etaleTopology B).over (B.obj hS)) (Type (max u (u + 1))) :=
    ⟨yoneda.obj U ⋙ uliftFunctor.{u + 1}, hUL⟩ with hUF
  set FF : Sheaf ((etaleTopology B).over (B.obj hS)) (Type (max u (u + 1))) :=
    ⟨F ⋙ uliftFunctor.{u + 1}, hFL⟩ with hFF
  set QQ : Sheaf ((etaleTopology B).over (B.obj hS)) (Type (max u (u + 1))) :=
    ⟨Q.obj ⋙ uliftFunctor.{u + 1}, hQL⟩ with hQQ
  set φ : UF ⟶ FF := ⟨Functor.whiskerRight f uliftFunctor.{u + 1}⟩ with hφ
  set ψ : UF ⟶ QQ := ⟨Functor.whiskerRight q uliftFunctor.{u + 1}⟩ with hψ
  have hsurjφ : IsSurjectiveSheafType ((etaleTopology B).over (B.obj hS)) φ := by
    intro V ξ
    refine ⟨Presheaf.imageSieve f ξ.down,
      Presheaf.imageSieve_mem ((etaleTopology B).over (B.obj hS)) f ξ.down, ?_⟩
    intro W k hk
    obtain ⟨x, hx⟩ := hk
    exact ⟨ULift.up x, congrArg ULift.up hx⟩
  have hsurjψ : IsSurjectiveSheafType ((etaleTopology B).over (B.obj hS)) ψ := by
    intro V ξ
    refine ⟨Presheaf.imageSieve q ξ.down,
      Presheaf.imageSieve_mem ((etaleTopology B).over (B.obj hS)) q ξ.down, ?_⟩
    intro W k hk
    obtain ⟨x, hx⟩ := hk
    exact ⟨ULift.up x, congrArg ULift.up hx⟩
  -- The two maps identify the same pairs of points of `U`, having the same kernel pair.
  have hFQ : ∀ {V : BigFppfOver B S hS} (x y : V ⟶ U),
      f.app (op V) x = f.app (op V) y → q.app (op V) x = q.app (op V) y := fun x y hxy ↦
    app_eq_of_app_eq_of_isPullback hpull hqpull.w hxy
  have hQF : ∀ {V : BigFppfOver B S hS} (x y : V ⟶ U),
      q.app (op V) x = q.app (op V) y → f.app (op V) x = f.app (op V) y := fun x y hxy ↦
    app_eq_of_app_eq_of_isPullback hqpull hpull.w hxy
  have hcondψ : pullback.fst φ φ ≫ ψ = pullback.snd φ φ ≫ ψ := by
    apply Sheaf.hom_ext
    ext ⟨V⟩ p
    have h₁ : φ.hom.app (op V) ((pullback.fst φ φ).hom.app (op V) p) =
        φ.hom.app (op V) ((pullback.snd φ φ).hom.app (op V) p) :=
      congrArg (fun η : pullback φ φ ⟶ FF ↦ η.hom.app (op V) p)
        (pullback.condition (f := φ) (g := φ))
    exact congrArg ULift.up (hFQ _ _ (congrArg ULift.down h₁))
  have hcondφ : pullback.fst ψ ψ ≫ φ = pullback.snd ψ ψ ≫ φ := by
    apply Sheaf.hom_ext
    ext ⟨V⟩ p
    have h₁ : ψ.hom.app (op V) ((pullback.fst ψ ψ).hom.app (op V) p) =
        ψ.hom.app (op V) ((pullback.snd ψ ψ).hom.app (op V) p) :=
      congrArg (fun η : pullback ψ ψ ⟶ QQ ↦ η.hom.app (op V) p)
        (pullback.condition (f := ψ) (g := ψ))
    exact congrArg ULift.up (hQF _ _ (congrArg ULift.down h₁))
  -- Both are coequalizers of their common kernel pair, hence isomorphic.
  have hcolφ := Classical.choice
    (coequalizer_of_surjection ((etaleTopology B).over (B.obj hS)) φ hsurjφ)
  have hcolψ := Classical.choice
    (coequalizer_of_surjection ((etaleTopology B).over (B.obj hS)) ψ hsurjψ)
  set a : FF ⟶ QQ := hcolφ.desc (Cofork.ofπ ψ hcondψ) with ha
  set b : QQ ⟶ FF := hcolψ.desc (Cofork.ofπ φ hcondφ) with hb
  have hfacφ : φ ≫ a = ψ := by
    have := hcolφ.fac (Cofork.ofπ ψ hcondψ) WalkingParallelPair.one
    simpa [coequalizerCofork] using this
  have hfacψ : ψ ≫ b = φ := by
    have := hcolψ.fac (Cofork.ofπ φ hcondφ) WalkingParallelPair.one
    simpa [coequalizerCofork] using this
  have hab : a ≫ b = 𝟙 FF := by
    refine Cofork.IsColimit.hom_ext hcolφ ?_
    simp only [coequalizerCofork, Cofork.π_ofπ]
    rw [← Category.assoc, hfacφ, hfacψ]
    exact (Category.comp_id φ).symm
  have hba : b ≫ a = 𝟙 QQ := by
    refine Cofork.IsColimit.hom_ext hcolψ ?_
    simp only [coequalizerCofork, Cofork.π_ofπ]
    rw [← Category.assoc, hfacψ, hfacφ]
    exact (Category.comp_id ψ).symm
  -- Transport the fppf sheaf condition from the quotient sheaf back to `F`.
  have hiso : (F ⋙ uliftFunctor.{u + 1}) ≅ (Q.obj ⋙ uliftFunctor.{u + 1}) :=
    (sheafToPresheaf _ _).mapIso ⟨a, b, hab, hba⟩
  refine ⟨?_, hdiag, ⟨U, f, hsurj, hetale⟩⟩
  refine Presheaf.isSheaf_of_isSheaf_comp _ _ uliftFunctor.{u + 1} ?_
  exact (Presheaf.isSheaf_of_iso_iff hiso).mpr
    (Presheaf.isSheaf_comp_of_isSheaf _ _ uliftFunctor.{u + 1} Q.property)

/-- **Stacks 076M, granted Stacks 02WW.** A presheaf of sets on the big fppf category over `S`
which is a sheaf for the chosen étale topology, whose diagonal is representable and which admits
a surjective étale atlas by a scheme is an algebraic space over `S`.

The hypothesis `hquot` is the conclusion of Stacks 02WW. It is consumed only through the
representability of `AlgebraicGeometry.Space.quotientMap`, and then only to reach the
étale-local surjectivity which
`AlgebraicGeometry.Space.isAlgebraicSpace_of_isSheaf_etale_of_isLocallySurjective_quotientMap`
asks for directly; that sharper form is the one to use. Neither form carries `@[stacks 076M]`:
both are weaker than the source, which proves the result outright. -/
theorem isAlgebraicSpace_of_isSheaf_etale_of_isAlgebraicSpace_quotientSheaf
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : Presheaf.IsSheaf ((etaleTopology B).over (B.obj hS)) F)
    (hdiag : yoneda.relativelyRepresentable (diag F))
    (hatlas : ∃ (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ F),
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf f ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf f)
    (hquot : ∀ {R U : BigFppfOver B S hS} (s t : R ⟶ U),
      IsEtaleEquivalenceRelation (relation B S hS s t) →
        IsAlgebraicSpace B S hS
          (quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
            (relation B S hS s t)).obj) :
    IsAlgebraicSpace B S hS F := by
  refine isAlgebraicSpace_of_isSheaf_etale_of_isLocallySurjective_quotientMap
    B S hS F hF hdiag hatlas fun {R U} s t hj ↦ ?_
  have := hj
  have hrep : yoneda.relativelyRepresentable (quotientMap B S hS s t) :=
    relativelyRepresentable_quotientMap_of_isAlgebraicSpace B S hS s t (hquot s t hj)
  exact isLocallySurjective_etaleTopology_of_presheaf B S hS (quotientMap B S hS s t)
    (quotientMap_surjective B S hS s t hrep) (quotientMap_etale B S hS s t hrep)

end AlgebraicGeometry.Space

end
