module

public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Gluing an isomorphism of schemes from isomorphisms on an open cover

Let `X` and `Y` be schemes, let `V i` be an open cover of `Y` and `U i` an open cover of `X`
indexed by the same set, and suppose given isomorphisms `f i : V i ≅ U i` of the corresponding
open subschemes.  This file assembles the `f i` into a single isomorphism `g : Y ≅ X` restricting
to each `f i`, under the two overlap-compatibility hypotheses that are exactly necessary for that
to hold.

The two hypotheses are
`∀ i j, (V i ⊓ V j → V i → X) = (V i ⊓ V j → V j → X)` and the mirror statement
`∀ i j, (U i ⊓ U j → U i → Y) = (U i ⊓ U j → U j → Y)`, the second taken with respect to the
inverses `(f i).inv`.  **Both** are needed: with `X` a one-point scheme, `U 1 = U 2 = X` and `Y`
the disjoint union of two points covered by `V 1`, `V 2`, the first hypothesis holds vacuously
(`V 1 ⊓ V 2 = ⊥`) while no isomorphism `Y ≅ X` exists, and it is the second hypothesis that
fails.  `AlgebraicGeometry.homOfLE_comp_eq_of_schemeIso_restrict` and
`AlgebraicGeometry.homOfLE_comp_inv_eq_of_schemeIso_restrict` are the converses: a global
isomorphism restricting to the `f i` satisfies both, so neither hypothesis is stronger than the
conclusion.

## Main results

* `AlgebraicGeometry.pullback_fst_comp_eq_snd_comp_of_homOfLE_comp_eq` — the translation between
  the "intersection of two opens" spelling of a gluing condition and the fibre-product spelling
  that `AlgebraicGeometry.Scheme.Cover.glueMorphisms` asks for.
* `AlgebraicGeometry.exists_schemeIso_of_isOpenCover_of_overlapCompatible` — the gluing itself:
  the single isomorphism `g : Y ≅ X` together with the two factorisations through the charts.
* `AlgebraicGeometry.ι_comp_inv_eq_of_ι_comp_hom_eq`,
  `AlgebraicGeometry.homOfLE_comp_eq_of_schemeIso_restrict` and
  `AlgebraicGeometry.homOfLE_comp_inv_eq_of_schemeIso_restrict` — the converses.

## Relation to [Stacks, Tag 0GPJ]

The conclusion of [Stacks, Tag 0GPJ] is a *single* isomorphism of schemes together with a
*single* invertible module; what
`AlgebraicGeometry.exists_isOpenCover_schemeIso_invertibleSheaf_of_isAffineOpenCover` proves is
the per-chart form, an affine open cover `U i` of `X`, opens `V i` covering `Y`, and for each `i`
an isomorphism `f i : V i ≅ U i` and an invertible module `L i`.  The Stacks source dismisses the
passage from one to the other with "We omit the details".

This file supplies the scheme half of that passage **as a reduction**: it isolates the two
overlap compatibilities as hypotheses and proves that they are precisely what is missing, the
converses above showing that nothing stronger has been assumed.

The forward compatibility `hVcompat` IS now discharged for the reconstruction's own charts, by
`AlgebraicGeometry.exists_isOpenCover_schemeIso_overlapCompatible_of_isAffineOpenCover`
(`QuasiCoherent/ReconstructionOverlapCompatible.lean:256`).  The charts do come out by
existential choice, so nothing about the choices themselves relates two indices; what relates
them is rigidity — the matched pair is canonical, `QuasiCoherent/ReconstructionRigidity.lean`
— together with the fact that an invertible sheaf on an affine scheme is a pullback of `tilde`
of an invertible module (`QuasiCoherent/AffineInvertiblePresentation.lean:162`).  Earlier
revisions of this note said that uniqueness statement was absent from the repository; it is not,
and the claim is withdrawn.

The mirror compatibility `hUcompat` is the remaining hypothesis.  Its enabling lemma — that the
inverse of a twisted pullback is again a twisted pullback by an invertible sheaf,
`QuasiCoherent/ReconstructionPairInverse.lean:349` — exists, so it is no longer circular.
Gluing the invertible modules `L i` is a further, separate descent problem, reduced in
`QuasiCoherent/ReconstructionGluedModule.lean` and not addressed here.

## References

* [Stacks Project, Proposition 56.6.6 (Tag 0GPJ)](https://stacks.math.columbia.edu/tag/0GPJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **From the intersection spelling of a gluing condition to the fibre-product spelling.**
Two morphisms `a` and `b` out of open subschemes `V` and `W` of `S` which agree after restriction
to `V ⊓ W` satisfy the compatibility condition over the fibre product `V ×_S W` that
`AlgebraicGeometry.Scheme.Cover.glueMorphisms` requires.

The fibre product maps to `V ⊓ W` by `AlgebraicGeometry.IsOpenImmersion.lift`, because its two
projections compose to the same morphism into `S`, whose image therefore lies in both `V` and
`W`; the two projections are recovered from that map by composing with the two inclusions of
`V ⊓ W`. -/
theorem pullback_fst_comp_eq_snd_comp_of_homOfLE_comp_eq {S T : Scheme.{u}} {V W : S.Opens}
    (a : V.toScheme ⟶ T) (b : W.toScheme ⟶ T)
    (h : S.homOfLE (inf_le_left : V ⊓ W ≤ V) ≫ a = S.homOfLE (inf_le_right : V ⊓ W ≤ W) ≫ b) :
    pullback.fst V.ι W.ι ≫ a = pullback.snd V.ι W.ι ≫ b := by
  have hcond : pullback.fst V.ι W.ι ≫ V.ι = pullback.snd V.ι W.ι ≫ W.ι := pullback.condition
  have hrange : Set.range (pullback.fst V.ι W.ι ≫ V.ι) ⊆ Set.range (V ⊓ W : S.Opens).ι := by
    rw [Scheme.Opens.range_ι]
    rintro z ⟨x, rfl⟩
    refine Set.mem_inter ?_ ?_
    · rw [← Scheme.Opens.range_ι (U := V)]
      exact ⟨pullback.fst V.ι W.ι x, (Scheme.Hom.comp_apply _ _ _).symm⟩
    · rw [← Scheme.Opens.range_ι (U := W), hcond]
      exact ⟨pullback.snd V.ι W.ι x, (Scheme.Hom.comp_apply _ _ _).symm⟩
  set r := IsOpenImmersion.lift (V ⊓ W : S.Opens).ι (pullback.fst V.ι W.ι ≫ V.ι) hrange with hr
  have hrι : r ≫ (V ⊓ W : S.Opens).ι = pullback.fst V.ι W.ι ≫ V.ι := by
    rw [hr]; exact IsOpenImmersion.lift_fac _ _ _
  have hleft : r ≫ S.homOfLE (inf_le_left : V ⊓ W ≤ V) = pullback.fst V.ι W.ι := by
    rw [← cancel_mono V.ι, Category.assoc, Scheme.homOfLE_ι, hrι]
  have hright : r ≫ S.homOfLE (inf_le_right : V ⊓ W ≤ W) = pullback.snd V.ι W.ι := by
    rw [← cancel_mono W.ι, Category.assoc, Scheme.homOfLE_ι, hrι]
    exact hcond
  rw [← hleft, ← hright, Category.assoc, Category.assoc, h]

/-- Morphisms out of the members of an open cover that agree on the overlaps glue to a morphism. -/
private theorem exists_comp_eq_of_homOfLE_comp_eq {S T : Scheme.{u}} {ι : Type*} (V : ι → S.Opens)
    (hV : IsOpenCover V) (a : ∀ i, (V i).toScheme ⟶ T)
    (h : ∀ i j, S.homOfLE (inf_le_left : V i ⊓ V j ≤ V i) ≫ a i =
      S.homOfLE (inf_le_right : V i ⊓ V j ≤ V j) ≫ a j) :
    ∃ g : S ⟶ T, ∀ i, (V i).ι ≫ g = a i :=
  ⟨(S.openCoverOfIsOpenCover V hV).glueMorphisms a
      (fun i j ↦ pullback_fst_comp_eq_snd_comp_of_homOfLE_comp_eq _ _ (h i j)),
    fun i ↦ Scheme.Cover.ι_glueMorphisms (S.openCoverOfIsOpenCover V hV) _ _ i⟩

/-- If `gh` and `gi` restrict to `f.hom` and `f.inv` on the charts, then `gh ≫ gi` restricts to the
identity on `V`. -/
private theorem ι_comp_comp_eq_of_ι_comp_eq {X Y : Scheme.{u}} {V : Y.Opens} {U : X.Opens}
    (f : V.toScheme ≅ U.toScheme) (gh : Y ⟶ X) (gi : X ⟶ Y) (hgh : V.ι ≫ gh = f.hom ≫ U.ι)
    (hgi : U.ι ≫ gi = f.inv ≫ V.ι) : V.ι ≫ gh ≫ gi = V.ι := by
  rw [← Category.assoc, hgh, Category.assoc, hgi, ← Category.assoc, Iso.hom_inv_id,
    Category.id_comp]

/-- **Gluing a family of isomorphisms on an open cover into one isomorphism of schemes.**
Let `V i` be an open cover of `Y`, let `U i` be an open cover of `X` on the same index set, and
let `f i : V i ≅ U i` be isomorphisms of the open subschemes.  If the `f i` agree on the overlaps
`V i ⊓ V j` as morphisms into `X`, and the `(f i).inv` agree on the overlaps `U i ⊓ U j` as
morphisms into `Y`, then there is a single isomorphism `g : Y ≅ X` whose restriction to each
`V i` is `f i`.

Both overlap hypotheses are needed; see the module documentation for the two-point
counterexample to dropping the second, and
`AlgebraicGeometry.homOfLE_comp_eq_of_schemeIso_restrict`,
`AlgebraicGeometry.homOfLE_comp_inv_eq_of_schemeIso_restrict` for the converses. -/
theorem exists_schemeIso_of_isOpenCover_of_overlapCompatible {X Y : Scheme.{u}} {ι : Type*}
    (V : ι → Y.Opens) (U : ι → X.Opens) (hV : IsOpenCover V) (hU : IsOpenCover U)
    (f : ∀ i, (V i).toScheme ≅ (U i).toScheme)
    (hVcompat : ∀ i j, Y.homOfLE (inf_le_left : V i ⊓ V j ≤ V i) ≫ (f i).hom ≫ (U i).ι =
      Y.homOfLE (inf_le_right : V i ⊓ V j ≤ V j) ≫ (f j).hom ≫ (U j).ι)
    (hUcompat : ∀ i j, X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ (f i).inv ≫ (V i).ι =
      X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ (f j).inv ≫ (V j).ι) :
    ∃ g : Y ≅ X, (∀ i, (V i).ι ≫ g.hom = (f i).hom ≫ (U i).ι) ∧
      ∀ i, (U i).ι ≫ g.inv = (f i).inv ≫ (V i).ι := by
  let 𝒱 : Y.OpenCover := Y.openCoverOfIsOpenCover V hV
  let 𝒰 : X.OpenCover := X.openCoverOfIsOpenCover U hU
  obtain ⟨gh, hgh⟩ := exists_comp_eq_of_homOfLE_comp_eq V hV _ hVcompat
  obtain ⟨gi, hgi⟩ := exists_comp_eq_of_homOfLE_comp_eq U hU _ hUcompat
  refine ⟨⟨gh, gi, 𝒱.hom_ext _ _ fun i ↦ ?_, 𝒰.hom_ext _ _ fun i ↦ ?_⟩, hgh, hgi⟩
  · rw [Category.comp_id]
    exact ι_comp_comp_eq_of_ι_comp_eq (f i) gh gi (hgh i) (hgi i)
  · rw [Category.comp_id]
    exact ι_comp_comp_eq_of_ι_comp_eq (f i).symm gi gh (hgi i) (hgh i)

/-- If a global isomorphism `g : Y ≅ X` restricts to `f i` on the chart `V i`, then `g.inv`
restricts to `(f i).inv` on `U i`. -/
theorem ι_comp_inv_eq_of_ι_comp_hom_eq {X Y : Scheme.{u}} {V : Y.Opens} {U : X.Opens}
    (f : V.toScheme ≅ U.toScheme) (g : Y ≅ X) (hg : V.ι ≫ g.hom = f.hom ≫ U.ι) :
    U.ι ≫ g.inv = f.inv ≫ V.ι := by
  rw [Iso.comp_inv_eq, Category.assoc, hg, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- **The first overlap hypothesis is necessary.**  A global isomorphism `g : Y ≅ X` restricting
to the charts `f i` makes the `f i` agree on the overlaps `V i ⊓ V j`: both composites are the
inclusion of `V i ⊓ V j` followed by `g.hom`. -/
theorem homOfLE_comp_eq_of_schemeIso_restrict {X Y : Scheme.{u}} {ι : Type*} (V : ι → Y.Opens)
    (U : ι → X.Opens) (f : ∀ i, (V i).toScheme ≅ (U i).toScheme) (g : Y ≅ X)
    (hg : ∀ i, (V i).ι ≫ g.hom = (f i).hom ≫ (U i).ι) (i j : ι) :
    Y.homOfLE (inf_le_left : V i ⊓ V j ≤ V i) ≫ (f i).hom ≫ (U i).ι =
      Y.homOfLE (inf_le_right : V i ⊓ V j ≤ V j) ≫ (f j).hom ≫ (U j).ι := by
  rw [← hg i, ← hg j, ← Category.assoc, ← Category.assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι]

/-- **The second overlap hypothesis is necessary.**  A global isomorphism `g : Y ≅ X` restricting
to the charts `f i` makes the `(f i).inv` agree on the overlaps `U i ⊓ U j`. -/
theorem homOfLE_comp_inv_eq_of_schemeIso_restrict {X Y : Scheme.{u}} {ι : Type*}
    (V : ι → Y.Opens) (U : ι → X.Opens) (f : ∀ i, (V i).toScheme ≅ (U i).toScheme) (g : Y ≅ X)
    (hg : ∀ i, (V i).ι ≫ g.hom = (f i).hom ≫ (U i).ι) (i j : ι) :
    X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ (f i).inv ≫ (V i).ι =
      X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ (f j).inv ≫ (V j).ι := by
  rw [← ι_comp_inv_eq_of_ι_comp_hom_eq (f i) g (hg i),
    ← ι_comp_inv_eq_of_ι_comp_hom_eq (f j) g (hg j), ← Category.assoc, ← Category.assoc,
    Scheme.homOfLE_ι, Scheme.homOfLE_ι]

end AlgebraicGeometry

end
