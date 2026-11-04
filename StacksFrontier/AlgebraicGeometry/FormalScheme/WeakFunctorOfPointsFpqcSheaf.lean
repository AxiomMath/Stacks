module

public import StacksFrontier.AlgebraicGeometry.FormalScheme.WeakFormalSpectrumFpqcDescent

/-!
# McQuillan formal schemes are fpqc sheaves

Stacks 0AI3 records that the counterparts of Lemmas 87.2.1 and 87.2.2 hold for the larger
category of formal schemes built on weak admissibility, with the same proofs. This file completes
the counterpart of Lemma 87.2.2: the functor of points of a McQuillan formal scheme satisfies the
sheaf condition for fpqc coverings, on the category of all schemes and on the schemes `Sch_κ` of
size below a cutoff.

The separatedness half was already available as
`AlgebraicGeometry.isSeparated_fpqcTopology_mcQuillanFormalSchemePoints`, and the affine descent
step as `AlgebraicGeometry.exists_comp_eq_of_flat_surjective_spfwLTRS`. What is added here is the
*existence* of amalgamations: the reduction of the sheaf condition to one faithfully flat
morphism of affines, the affine case for McQuillan's formal spectrum itself, the descent of a
family landing in one weak affine formal chart, and the chart-by-chart gluing.

The argument is the source's, and the one already carried out for admissible rings in
`StacksFrontier.AlgebraicGeometry.FormalScheme.FunctorOfPointsFpqcDescent`. For a general `𝔛` the
underlying continuous map descends first, continuous maps into a fixed space forming an fpqc
sheaf; over the preimage of a weak affine formal chart `𝔘 ≅ Spfw A` the family lands in `𝔘`, so
it descends by the affine case; and the local amalgamations glue because the functor of points is
a Zariski sheaf (`AlgebraicGeometry.isSheaf_zariskiTopology_mcQuillanFormalSchemePoints`) and is
fpqc separated.

## Main definitions

* `AlgebraicGeometry.spfwMcQuillanFormalScheme`: McQuillan's formal spectrum of a weakly
  admissible topological ring as an object of the category of McQuillan formal schemes.

## Main results

* `AlgebraicGeometry.isMcQuillanFormalScheme_spfwLTRS`: McQuillan's formal spectrum is a formal
  scheme in the sense of McQuillan, being its own weak affine formal chart.
* `AlgebraicGeometry.isSheaf_fpqcTopology_mcQuillanFormalSchemePoints_spfw`: the functor of points
  of McQuillan's formal spectrum is an fpqc sheaf.
* `AlgebraicGeometry.isSheaf_fpqcTopology_mcQuillanFormalSchemePoints`: **Stacks 0AI3**, the
  counterpart of Lemma 87.2.2 on the category of all schemes.
* `AlgebraicGeometry.isSheafFor_mcQuillanFormalSchemeFunctorOfPoints`: **Stacks 0AI3**, the
  counterpart of Lemma 87.2.2 for the functor of points on `Sch_κ`.

## References

* [Stacks Project, Tag 0AI3](https://stacks.math.columbia.edu/tag/0AI3)
* [Stacks Project, Tag 0AI2](https://stacks.math.columbia.edu/tag/0AI2)
* [Stacks Project, Tag 022H](https://stacks.math.columbia.edu/tag/022H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopologicalRing

universe u

namespace AlgebraicGeometry

/-! ### McQuillan's formal spectrum as a McQuillan formal scheme -/

section Spfw

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A]

/-- McQuillan's formal spectrum of a weakly admissible topological ring is a formal scheme in the
sense of McQuillan: it is its own weak affine formal chart, exactly as the formal spectrum of an
admissible ring is its own affine formal chart in
`AlgebraicGeometry.isFormalScheme_spfLTRS`. -/
theorem isMcQuillanFormalScheme_spfwLTRS (hA : IsWeaklyAdmissible A) :
    IsMcQuillanFormalScheme (spfwLTRS A hA.1) := fun _ =>
  ⟨⊤, trivial, TopCommRingCat.of A, inferInstance, hA,
    ⟨PresheafedSpace.restrictTopIso _⟩⟩

/-- McQuillan's formal spectrum of a weakly admissible topological ring as an object of the
category of McQuillan formal schemes. -/
noncomputable def spfwMcQuillanFormalScheme (hA : IsWeaklyAdmissible A) :
    McQuillanFormalScheme.{u} :=
  ⟨spfwLTRS A hA.1, isMcQuillanFormalScheme_spfwLTRS A hA⟩

end Spfw

/-! ### Reduction of the fpqc sheaf condition to one affine descent -/

/-- For a faithfully flat morphism of affine schemes, the fpqc sheaf condition for the functor of
points of a McQuillan formal scheme on the one-element presieve it generates reduces to the
existence of amalgamations: uniqueness is the separatedness clause of the counterpart of
Lemma 87.2.2, already available as
`AlgebraicGeometry.isSeparated_fpqcTopology_mcQuillanFormalSchemePoints`. -/
theorem isSheafFor_singleton_of_exists_amalgamation_mcQuillanFormalSchemePoints
    (X : McQuillanFormalScheme.{u}) {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (hflat : Flat (Spec.map φ)) (hsurj : Surjective (Spec.map φ))
    (hex : ∀ x : Presieve.FamilyOfElements (mcQuillanFormalSchemePoints X)
        (Presieve.singleton (Spec.map φ)), x.Compatible → ∃ t, x.IsAmalgamation t) :
    Presieve.IsSheafFor (mcQuillanFormalSchemePoints X) (Presieve.singleton (Spec.map φ)) := by
  refine Presieve.IsSeparatedFor.isSheafFor ?_ hex
  rw [Presieve.isSeparatedFor_iff_generate]
  exact isSeparated_fpqcTopology_mcQuillanFormalSchemePoints X _
    (Scheme.Hom.generate_singleton_mem_propQCTopology (P := @Flat) (Spec.map φ) hflat)

/-- **The fpqc sheaf condition for the functor of points of a McQuillan formal scheme, reduced to
one affine descent.** This is Stacks 022H applied to `AlgebraicGeometry.Scheme.fpqcTopology`,
which is the quasi-compact topology of the morphism property `AlgebraicGeometry.Flat`: a presheaf
of types is an fpqc sheaf exactly when it is a Zariski sheaf and satisfies the sheaf condition for
a single surjective flat morphism of affines. The Zariski half is
`AlgebraicGeometry.isSheaf_zariskiTopology_mcQuillanFormalSchemePoints`. -/
theorem isSheaf_fpqcTopology_mcQuillanFormalSchemePoints_of_affine
    (X : McQuillanFormalScheme.{u})
    (haff : ∀ {R S : CommRingCat.{u}} (φ : R ⟶ S), Flat (Spec.map φ) →
      Surjective (Spec.map φ) →
      Presieve.IsSheafFor (mcQuillanFormalSchemePoints X) (Presieve.singleton (Spec.map φ))) :
    Presieve.IsSheaf Scheme.fpqcTopology.{u} (mcQuillanFormalSchemePoints X) :=
  have : IsZariskiLocalAtSource (@Flat : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  (isSheaf_type_propQCTopology_iff (P := (@Flat : MorphismProperty Scheme.{u}))
    (mcQuillanFormalSchemePoints X)).mpr
      ⟨isSheaf_zariskiTopology_mcQuillanFormalSchemePoints X, fun φ hf hs => haff φ hf hs⟩

/-- **The fpqc sheaf condition for the functor of points of a McQuillan formal scheme, reduced to
one affine descent, existence only.** The functor of points is an fpqc sheaf as soon as, for every
faithfully flat morphism `Spec S ⟶ Spec R` of affine schemes, a compatible family of points over
`Spec S` admits *some* amalgamation over `Spec R`: uniqueness is the separatedness of
`AlgebraicGeometry.isSeparated_fpqcTopology_mcQuillanFormalSchemePoints`, and the Zariski case is
`AlgebraicGeometry.isSheaf_zariskiTopology_mcQuillanFormalSchemePoints`. -/
theorem isSheaf_fpqcTopology_mcQuillanFormalSchemePoints_of_exists_affine
    (X : McQuillanFormalScheme.{u})
    (hex : ∀ {R S : CommRingCat.{u}} (φ : R ⟶ S), Flat (Spec.map φ) →
      Surjective (Spec.map φ) →
      ∀ x : Presieve.FamilyOfElements (mcQuillanFormalSchemePoints X)
        (Presieve.singleton (Spec.map φ)), x.Compatible → ∃ t, x.IsAmalgamation t) :
    Presieve.IsSheaf Scheme.fpqcTopology.{u} (mcQuillanFormalSchemePoints X) :=
  isSheaf_fpqcTopology_mcQuillanFormalSchemePoints_of_affine X fun φ hf hs =>
    isSheafFor_singleton_of_exists_amalgamation_mcQuillanFormalSchemePoints X φ hf hs (hex φ hf hs)

/-! ### Points of McQuillan's formal spectrum descend along fpqc coverings -/

section SpfwSheaf

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A]

/-- **The functor of points of McQuillan's formal spectrum is an fpqc sheaf.** For a weakly
admissible topological ring `A`, the functor of points of `Spfw A` on the category of all schemes
satisfies the sheaf condition for fpqc coverings.

This is the source's proof of Lemma 87.2.2 unchanged: the sheaf condition reduces to the Zariski
case, which is `AlgebraicGeometry.isSheaf_zariskiTopology_mcQuillanFormalSchemePoints`, together
with descent along one faithfully flat morphism of affine schemes, which is
`AlgebraicGeometry.exists_comp_eq_of_flat_surjective_spfwLTRS`. -/
theorem isSheaf_fpqcTopology_mcQuillanFormalSchemePoints_spfw (hA : IsWeaklyAdmissible A) :
    Presieve.IsSheaf Scheme.fpqcTopology.{u}
      (mcQuillanFormalSchemePoints (spfwMcQuillanFormalScheme A hA)) := by
  refine isSheaf_fpqcTopology_mcQuillanFormalSchemePoints_of_exists_affine _
    fun {R S} φ hflat hsurj x hx => ?_
  rw [Presieve.FamilyOfElements.compatible_singleton_iff] at hx
  have hbridge : ∀ {Z W : Scheme.{u}} (p : Z ⟶ W),
      (schemeToMcQuillanFormalScheme.map p).hom = schemeToLTRS.map p := fun _ => rfl
  obtain ⟨t, ht⟩ := exists_comp_eq_of_flat_surjective_spfwLTRS A hA φ hflat hsurj
    (x _ ⟨⟩).hom fun {Z} p₁ p₂ hp => by
      rw [← hbridge p₁, ← hbridge p₂]
      exact congrArg InducedCategory.Hom.hom (hx p₁ p₂ hp)
  refine ⟨ObjectProperty.homMk t, (Presieve.FamilyOfElements.isAmalgamation_singleton_iff
    _ _ _).2 (InducedCategory.hom_ext ?_)⟩
  exact (congrArg (· ≫ t) (hbridge (Spec.map φ))).trans ht

end SpfwSheaf

/-! ### Points landing in a weak affine formal chart -/

/-- **Descent of points landing in a weak affine formal chart.** Let `𝔛|_𝔘 ≅ Spfw A` be a weak
affine formal chart of a McQuillan formal scheme `𝔛`. A compatible family of points of `𝔛` on an
fpqc covering sieve, all of whose members land in `𝔘`, has an amalgamation: the family factors
through `𝔛|_𝔘 ≅ Spfw A`, the inclusion of `𝔘` being a monomorphism, and the functor of points of
`Spfw A` is an fpqc sheaf by
`AlgebraicGeometry.isSheaf_fpqcTopology_mcQuillanFormalSchemePoints_spfw`. -/
theorem exists_isAmalgamation_of_range_subset_weakChart {X : McQuillanFormalScheme.{u}}
    (U : Opens X.obj)
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : IsWeaklyAdmissible A) (χ : X.obj.restrict U ≅ spfwLTRS A hA.1)
    {T : Scheme.{u}} {S : Sieve T} (hS : S ∈ Scheme.fpqcTopology.{u} T)
    {x : Presieve.FamilyOfElements (mcQuillanFormalSchemePoints X) S.arrows} (hx : x.Compatible)
    (hrange : ∀ ⦃Z : Scheme.{u}⦄ (f : Z ⟶ T) (hf : S f),
      Set.range (x f hf).hom.toHom.base ⊆ Set.range (X.obj.ofRestrict U).toHom.base) :
    ∃ t, x.IsAmalgamation t := by
  let ι : spfwMcQuillanFormalScheme A hA ⟶ X := ObjectProperty.homMk (χ.inv ≫ X.obj.ofRestrict U)
  let y : Presieve.FamilyOfElements
      (mcQuillanFormalSchemePoints (spfwMcQuillanFormalScheme A hA)) S.arrows :=
    fun _ f hf => ObjectProperty.homMk (liftToRestrict U (x f hf).hom (hrange f hf) ≫ χ.hom)
  have hyι : ∀ ⦃Z : Scheme.{u}⦄ (f : Z ⟶ T) (hf : S f), y f hf ≫ ι = x f hf := fun Z f hf =>
    InducedCategory.hom_ext (by
      change (liftToRestrict U (x f hf).hom (hrange f hf) ≫ χ.hom) ≫ χ.inv ≫ X.obj.ofRestrict U
        = (x f hf).hom
      rw [Category.assoc, Iso.hom_inv_id_assoc, liftToRestrict_comp_ofRestrict])
  have hcancel : ∀ {W : Scheme.{u}}
      (a b : schemeToMcQuillanFormalScheme.obj W ⟶ spfwMcQuillanFormalScheme A hA),
      a ≫ ι = b ≫ ι → a = b := by
    intro W a b h
    have h' : a.hom ≫ χ.inv ≫ X.obj.ofRestrict U = b.hom ≫ χ.inv ≫ X.obj.ofRestrict U :=
      congrArg (fun m : schemeToMcQuillanFormalScheme.obj W ⟶ X => m.hom) h
    have h'' : (a.hom ≫ χ.inv) ≫ X.obj.ofRestrict U = (b.hom ≫ χ.inv) ≫ X.obj.ofRestrict U :=
      (Category.assoc _ _ _).trans (h'.trans (Category.assoc _ _ _).symm)
    have : Mono (X.obj.toPresheafedSpace.ofRestrict U.isOpenEmbedding) :=
      PresheafedSpace.ofRestrict_mono _ _ _
    have h2 : (a.hom ≫ χ.inv).toHom = (b.hom ≫ χ.inv).toHom :=
      (cancel_mono (X.obj.toPresheafedSpace.ofRestrict U.isOpenEmbedding)).1
        (congrArg LocallyTopologicallyRingedSpace.Hom.toHom h'')
    exact InducedCategory.hom_ext
      ((cancel_mono χ.inv).1 (LocallyTopologicallyRingedSpace.Hom.ext' h2))
  have hy : y.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ comm
    apply hcancel
    change (schemeToMcQuillanFormalScheme.map g₁ ≫ y f₁ h₁) ≫ ι
      = (schemeToMcQuillanFormalScheme.map g₂ ≫ y f₂ h₂) ≫ ι
    rw [Category.assoc, Category.assoc, hyι, hyι]
    exact hx g₁ g₂ h₁ h₂ comm
  obtain ⟨(s : schemeToMcQuillanFormalScheme.obj T ⟶ spfwMcQuillanFormalScheme A hA), hs, -⟩ :=
    isSheaf_fpqcTopology_mcQuillanFormalSchemePoints_spfw A hA S hS y hy
  refine ⟨s ≫ ι, fun Z f hf => ?_⟩
  have hsf : schemeToMcQuillanFormalScheme.map f ≫ s = y f hf := hs f hf
  change schemeToMcQuillanFormalScheme.map f ≫ s ≫ ι = x f hf
  rw [← Category.assoc, hsf, hyι]

/-! ### The counterpart of Lemma 87.2.2 for the fpqc topology -/

/-- **Stacks 0AI3**, the existence half of the counterpart of Lemma 87.2.2 in McQuillan's setting,
and so the full sheaf condition. The functor of points of a McQuillan formal scheme `𝔛`, on the
category of all schemes, satisfies the sheaf condition for fpqc coverings.

The proof is the source's, and is the one already carried out for admissible rings in
`AlgebraicGeometry.isSheaf_fpqcTopology_formalSchemePoints`. Uniqueness of amalgamations is
`AlgebraicGeometry.isSeparated_fpqcTopology_mcQuillanFormalSchemePoints`. For existence, a
compatible family of points first descends on underlying spaces to a continuous map `g : T → 𝔛`,
continuous maps into a fixed space forming an fpqc sheaf. Around each point `p` of `T` choose a
weak affine formal chart `𝔘 ≅ Spfw A` of `𝔛` containing `g p`; over the open `g⁻¹ 𝔘` every member
of the pulled-back family lands in `𝔘`, so it has an amalgamation by
`AlgebraicGeometry.exists_isAmalgamation_of_range_subset_weakChart`. These local amalgamations
glue because the functor of points is a Zariski sheaf
(`AlgebraicGeometry.isSheaf_zariskiTopology_mcQuillanFormalSchemePoints`). -/
@[stacks 0AI3 "the counterpart of Lemma 87.2.2: the functor of points of a McQuillan \
formal scheme on all schemes is a sheaf for the fpqc topology"]
theorem isSheaf_fpqcTopology_mcQuillanFormalSchemePoints (X : McQuillanFormalScheme.{u}) :
    Presieve.IsSheaf Scheme.fpqcTopology.{u} (mcQuillanFormalSchemePoints X) := by
  intro T S hS
  refine (isSeparated_fpqcTopology_mcQuillanFormalSchemePoints X S hS).isSheafFor fun x hx => ?_
  let z : Presieve.FamilyOfElements (continuousMapPresheaf (T := X.obj)) S.arrows :=
    fun _ f hf => (x f hf).hom.toHom.base.hom
  have hz : z.Compatible := fun Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ comm =>
    congrArg (fun m : schemeToMcQuillanFormalScheme.obj Z ⟶ X => m.hom.toHom.base.hom)
      (hx g₁ g₂ h₁ h₂ comm)
  have hC : Presieve.IsSheaf Scheme.fpqcTopology.{u} (continuousMapPresheaf (T := X.obj)) :=
    (isSheaf_iff_isSheaf_of_type _ _).1 (isSheaf_fpqcTopology_continuousMapPresheaf _)
  obtain ⟨(g : C(T, X.obj)), hg, -⟩ := hC S hS z hz
  choose U hxU A hlin hdata using X.property
  let V : T → T.Opens := fun p =>
    ⟨g ⁻¹' (U (g p) : Set X.obj), (U (g p)).isOpen.preimage g.continuous⟩
  have hV : IsOpenCover V :=
    Opens.ext (Set.eq_univ_iff_forall.2 fun p => by
      rw [Opens.coe_iSup]
      exact Set.mem_iUnion.2 ⟨p, hxU (g p)⟩)
  refine Presieve.exists_isAmalgamation_of_locally
    (isSheaf_zariskiTopology_mcQuillanFormalSchemePoints X)
    (isSeparated_fpqcTopology_mcQuillanFormalSchemePoints X) hS hx
    (Precoverage.generate_mem_toGrothendieck (T.openCoverOfIsOpenCover V hV).mem₀) ?_
  rintro Y h ⟨W, k, _, ⟨p⟩, rfl⟩
  have := hlin (g p)
  refine exists_isAmalgamation_of_range_subset_weakChart (U (g p)) (A (g p)).α (hdata (g p)).1
    (ltrsIsoOfPresheafedSpaceIso (hdata (g p)).2.some)
    (Scheme.fpqcTopology.pullback_stable _ hS) (hx.pullback _) ?_
  rintro Z f hf _ ⟨w, rfl⟩
  refine ⟨⟨_, ?_⟩, rfl⟩
  have hw' : (x _ hf).hom.toHom.base w = g ((f ≫ k ≫ (T.openCoverOfIsOpenCover V hV).f p) w) :=
    (congrArg (fun c : C(Z, X.obj) => c w) (hg _ hf)).symm
  change (x _ hf).hom.toHom.base w ∈ U (g p)
  rw [hw']
  exact ((f ≫ k).base w).2

/-- **Stacks 0AI3**, the counterpart of Lemma 87.2.2 in McQuillan's setting for the functor of
points on the schemes of size below `κ`: it satisfies the sheaf condition for every family of
morphisms of `Sch_κ` which is an fpqc covering.

Members of `Sch_κ` have their fibre products in `Sch_κ`
(`AlgebraicGeometry.Scheme.size_pullback_lt`), so a family of points compatible on `Sch_κ` is
compatible on all schemes, and
`AlgebraicGeometry.isSheaf_fpqcTopology_mcQuillanFormalSchemePoints` applies. -/
@[stacks 0AI3 "the counterpart of Lemma 87.2.2: the functor of points of a McQuillan \
formal scheme on the schemes of size below the cutoff is a sheaf for the fpqc topology"]
theorem isSheafFor_mcQuillanFormalSchemeFunctorOfPoints {κ : Cardinal.{u}}
    (X : McQuillanFormalScheme.{u}) {T : (schemeCutoff κ).FullSubcategory} {R : Presieve T}
    (covering : R ∈ Scheme.fpqcPrecoverage.{u}.comap (schemeCutoff κ).ι T) :
    Presieve.IsSheafFor ((mcQuillanFormalSchemeFunctorOfPoints κ).obj X) R := by
  obtain ⟨J, S, u, rfl⟩ := R.exists_eq_ofArrows
  rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows] at covering
  simp only [ObjectProperty.ι_obj, ObjectProperty.ι_map] at covering
  have hsheaf : Presieve.IsSheafFor (mcQuillanFormalSchemePoints X)
      (Presieve.ofArrows (fun j => (S j).obj) fun j => (u j).hom) := by
    rw [Presieve.isSheafFor_iff_generate]
    exact isSheaf_fpqcTopology_mcQuillanFormalSchemePoints X _
      (Precoverage.generate_mem_toGrothendieck covering)
  rw [Presieve.isSheafFor_arrows_iff] at hsheaf ⊢
  intro x hx
  refine hsheaf x fun i j Z gi gj hij => ?_
  let P : (schemeCutoff κ).FullSubcategory :=
    ⟨pullback (u i).hom (u j).hom, Scheme.size_pullback_lt _ _ (S i).property (S j).property⟩
  have hP := hx i j P (ObjectProperty.homMk (pullback.fst _ _))
    (ObjectProperty.homMk (pullback.snd _ _)) (InducedCategory.hom_ext pullback.condition)
  let xi : schemeToMcQuillanFormalScheme.obj (S i).obj ⟶ X := x i
  let xj : schemeToMcQuillanFormalScheme.obj (S j).obj ⟶ X := x j
  have hP' : schemeToMcQuillanFormalScheme.map (pullback.fst (u i).hom (u j).hom) ≫ xi =
      schemeToMcQuillanFormalScheme.map (pullback.snd (u i).hom (u j).hom) ≫ xj := hP
  change schemeToMcQuillanFormalScheme.map gi ≫ xi = schemeToMcQuillanFormalScheme.map gj ≫ xj
  rw [← pullback.lift_fst gi gj hij, Functor.map_comp, Category.assoc, hP', ← Category.assoc,
    ← Functor.map_comp, pullback.lift_snd]

end AlgebraicGeometry

end
