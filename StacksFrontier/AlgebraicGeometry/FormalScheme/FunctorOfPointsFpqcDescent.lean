module

public import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
public import StacksFrontier.AlgebraicGeometry.FormalScheme.FunctorOfPointsFpqcReduction
public import StacksFrontier.AlgebraicGeometry.FormalScheme.FunctorOfPointsFull

/-!
# Formal schemes are fpqc sheaves

Let `𝔛` be a formal scheme. Stacks 0AI2 says that its functor of points
`h_𝔛(T) = Mor_{Formal Schemes}(T, 𝔛)` satisfies the sheaf condition for fpqc coverings. The
separatedness half is `AlgebraicGeometry.isSeparated_fpqcTopology_formalSchemePoints`; this file
proves that a compatible family of points over an fpqc covering has an amalgamation, and so the
full statement, both on the category of all schemes and on the schemes `Sch_κ` of size below a
cutoff, where Stacks 0AI1 defines `h_𝔛`.

The argument follows the source's. For a formal spectrum `Spf A` and a faithfully flat
`Spec S → Spec R`, a point `Spec S → Spf A` factors through some `Spec (A/I)`
(`AlgebraicGeometry.exists_factor_spfQuotientPointOn`); the factorisation inherits the descent
condition because a morphism to `Spec (A/I)` is determined by the point of `Spf A` it induces,
and it descends because the fpqc topology is subcanonical. This replaces the source's appeal to
the equalizer `R → S ⇉ S ⊗_R S` (Stacks 023M) by Mathlib's effective epimorphism statement for
faithfully flat morphisms, of which it is the affine case. Together with the Zariski case, Stacks
022H gives the sheaf condition for `Spf A`.

For a general `𝔛` the source descends the underlying map first (Stacks 02KI, 02JY). Here that is
the fpqc sheaf property of continuous maps into a fixed space
(`AlgebraicGeometry.isSheaf_fpqcTopology_continuousMapPresheaf`). Over the preimage of an affine
formal chart `𝔘 ≅ Spf A` the family lands in `𝔘`, so it descends by the affine case, and the
local amalgamations glue because `h_𝔛` is a Zariski sheaf and is fpqc separated
(`CategoryTheory.Presieve.exists_isAmalgamation_of_locally`). This is the gluing the source
leaves to the reader.

## Main results

* `CategoryTheory.Presieve.exists_isAmalgamation_of_locally`: for a presheaf which is a sheaf for
  `J` and separated for `K`, a compatible family on a `K`-covering sieve has an amalgamation as
  soon as it has one locally for `J`.
* `AlgebraicGeometry.isSheaf_fpqcTopology_formalSchemePoints_spfFormalScheme`: the functor of
  points of a formal spectrum is an fpqc sheaf.
* `AlgebraicGeometry.isSheaf_fpqcTopology_formalSchemePoints`: the sheaf condition on the
  category of all schemes.
* `AlgebraicGeometry.isSheafFor_formalSchemeFunctorOfPoints`: **Stacks 0AI2**, for the functor of
  points on `Sch_κ` of Stacks 0AI1 and an fpqc covering family in `Sch_κ`.

## References

* [EGA I, Chapter I, Section 10]
* [Stacks Project, Tag 022H](https://stacks.math.columbia.edu/tag/022H)
* [Stacks Project, Tag 0AHZ](https://stacks.math.columbia.edu/tag/0AHZ)
* [Stacks Project, Tag 0AI1](https://stacks.math.columbia.edu/tag/0AI1)
* [Stacks Project, Tag 0AI2](https://stacks.math.columbia.edu/tag/0AI2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopologicalRing

universe u

namespace CategoryTheory.Presieve

variable {C : Type*} [Category* C] {P : Cᵒᵖ ⥤ Type*}

/-- **Local existence of amalgamations.** Let `P` be a sheaf for a topology `J` and separated for
a topology `K`. A compatible family of elements of `P` on a `K`-covering sieve `S` has an
amalgamation as soon as it has one locally for `J`: when there is a `J`-covering sieve `R` such
that for every `h ∈ R` the family pulled back along `h` has an amalgamation. -/
theorem exists_isAmalgamation_of_locally {J K : GrothendieckTopology C}
    (hJ : IsSheaf J P) (hK : IsSeparated K P) {X : C} {S : Sieve X} (hS : S ∈ K X)
    {x : FamilyOfElements P S.arrows} (hx : x.Compatible) {R : Sieve X} (hR : R ∈ J X)
    (hloc : ∀ ⦃Y : C⦄ ⦃h : Y ⟶ X⦄, R h → ∃ t, (x.pullback h).IsAmalgamation t) :
    ∃ t, x.IsAmalgamation t := by
  choose t ht using hloc
  let y : FamilyOfElements P R.arrows := fun _ _ hh => t hh
  have hy : y.Compatible := by
    rw [compatible_iff_sieveCompatible]
    intro Y Z h k hh
    refine hK _ (K.pullback_stable (k ≫ h) hS) (x.pullback (k ≫ h)) _ _
      (ht (R.downward_closed hh k)) ?_
    intro W g hg
    rw [← Functor.map_comp_apply, ← op_comp]
    exact (ht hh (g ≫ k) (by simpa using hg)).trans
      (by dsimp only [FamilyOfElements.pullback]; congr 1; simp)
  obtain ⟨u, hu, -⟩ := hJ R hR y hy
  refine ⟨u, fun Z s hs => ?_⟩
  refine (hJ _ (J.pullback_stable s hR)).isSeparatedFor.ext fun W k hk => ?_
  rw [← Functor.map_comp_apply, ← op_comp, hu (k ≫ s) hk,
    ← hx.to_sieveCompatible s k hs]
  have h1 := ht hk (𝟙 W) (by simpa using S.downward_closed hs k)
  rw [op_id, Functor.map_id_apply] at h1
  exact h1.trans (by dsimp only [FamilyOfElements.pullback]; congr 1; simp)

end CategoryTheory.Presieve

namespace AlgebraicGeometry

/-! ### Points of a formal spectrum descend along faithfully flat morphisms -/

section Spf

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- Two morphisms from a scheme to `Spec (A/I)` agree as soon as they induce the same point of
`Spf A`: both are determined by the ring map they induce on global sections, and these agree
after the surjection `A → A/I`. -/
theorem schemeToFormalScheme_map_comp_spfQuotientPointOn_injective {P : Ideal A → Prop}
    [IsWeakIdealSystem A P] (I₀ : SpfIndex A P)
    (I : SpfIndex A P) {T : Scheme.{u}} {a b : T ⟶ Spec (spfQuotientOn A I)}
    (h : (schemeToFormalScheme.map a).hom ≫ spfQuotientPointOn A I₀ I =
      (schemeToFormalScheme.map b).hom ≫ spfQuotientPointOn A I₀ I) : a = b := by
  have hgamma :
      spfGammaComponentHomOn A I ≫ a.appTop = spfGammaComponentHomOn A I ≫ b.appTop := by
    rw [← spfPointGammaHomOn_comp_spfQuotientPointOn A I₀ I a,
      ← spfPointGammaHomOn_comp_spfQuotientPointOn A I₀ I b]
    exact congrArg (spfPointGammaHomOn A) h
  have hepi : Epi (spfGammaComponentHomOn A I) := by
    rw [spfGammaComponentHomOn]
    have : Epi (CommRingCat.ofHom (Ideal.Quotient.mk I.1)) :=
      ConcreteCategory.epi_of_surjective _ Ideal.Quotient.mk_surjective
    infer_instance
  exact ext_of_isAffine ((cancel_epi _).1 hgamma)

/-- Two morphisms from a scheme to `Spec (A/I)` agree as soon as they induce the same point of
`Spf A`: both are determined by the ring map they induce on global sections, and these agree
after the surjection `A → A/I`.

The ideals-of-definition case of `schemeToFormalScheme_map_comp_spfQuotientPointOn_injective`. -/
theorem schemeToFormalScheme_map_comp_spfQuotientPoint_injective (hA : IsPreAdmissible A)
    (I : IdealsOfDefinition A) {T : Scheme.{u}} {a b : T ⟶ Spec (spfQuotient A I)}
    (h : (schemeToFormalScheme.map a).hom ≫ spfQuotientPoint A hA I =
      (schemeToFormalScheme.map b).hom ≫ spfQuotientPoint A hA I) : a = b :=
  schemeToFormalScheme_map_comp_spfQuotientPointOn_injective A (P := IsIdealOfDefinition)
    (preAdmissibleSpfIndex A hA) I h

/-- The underlying morphism of `schemeToFormalScheme.map (f ≫ g)` is the composite of those of
`schemeToFormalScheme.map f` and `schemeToFormalScheme.map g`. -/
@[reassoc]
theorem schemeToFormalScheme_map_comp_hom {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (schemeToFormalScheme.map (f ≫ g)).hom =
      (schemeToFormalScheme.map f).hom ≫ (schemeToFormalScheme.map g).hom :=
  (congrArg (fun m : schemeToFormalScheme.obj X ⟶ schemeToFormalScheme.obj Z => m.hom)
    (schemeToFormalScheme.map_comp f g)).trans
    (ObjectProperty.FullSubcategory.comp_hom (f := _) (g := _))

variable [IsLinearTopology A A]

/-- **The functor of points of a formal spectrum is an fpqc sheaf.** For an admissible
topological ring `A`, a point of `Spf A` over `Spec S` whose two pullbacks to
`Spec (S ⊗_R S)` agree descends along a faithfully flat `Spec S → Spec R`: it factors through
some `Spec (A/I)` by `AlgebraicGeometry.exists_factor_spfQuotientPointOn`, the factorisation
inherits the descent condition because `Spec (A/I) → Spf A` is injective on points, and morphisms
of schemes descend along fpqc coverings, the fpqc topology being subcanonical. The Zariski case
and the reduction to this one are
`AlgebraicGeometry.isSheaf_fpqcTopology_formalSchemePoints_of_affine`. -/
theorem isSheaf_fpqcTopology_formalSchemePoints_spfFormalScheme (hA : IsAdmissible A) :
    Presieve.IsSheaf Scheme.fpqcTopology.{u} (formalSchemePoints (spfFormalScheme A hA)) := by
  refine isSheaf_fpqcTopology_formalSchemePoints_of_exists_affine _
    fun {R S} φ hflat hsurj x hx => ?_
  rw [Presieve.FamilyOfElements.compatible_singleton_iff] at hx
  obtain ⟨I, a, ha⟩ := exists_factor_spfQuotientPointOn A (preAdmissibleSpfIndex A hA.1)
    (isIso_spfGammaHom A hA) (Spec S) (x _ ⟨⟩).hom
  have hdesc : ∀ {Z : Scheme.{u}} (p₁ p₂ : Z ⟶ Spec S), p₁ ≫ Spec.map φ = p₂ ≫ Spec.map φ →
      p₁ ≫ a = p₂ ≫ a := by
    intro Z p₁ p₂ hp
    refine schemeToFormalScheme_map_comp_spfQuotientPointOn_injective A
      (preAdmissibleSpfIndex A hA.1) I ?_
    have hxp : (schemeToFormalScheme.map p₁).hom ≫ (x _ ⟨⟩).hom =
        (schemeToFormalScheme.map p₂).hom ≫ (x _ ⟨⟩).hom :=
      congrArg InducedCategory.Hom.hom (hx p₁ p₂ hp)
    have e : ∀ p : Z ⟶ Spec S, (schemeToFormalScheme.map (p ≫ a)).hom ≫
        spfQuotientPointOn A (preAdmissibleSpfIndex A hA.1) I =
          (schemeToFormalScheme.map p).hom ≫ (x _ ⟨⟩).hom := fun p =>
      (schemeToFormalScheme_map_comp_hom_assoc p a _).trans
        (congrArg ((schemeToFormalScheme.map p).hom ≫ ·) ha)
    exact (e p₁).trans (hxp.trans (e p₂).symm)
  have := hsurj
  have hsheaf := ((GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
      (J := Scheme.fpqcTopology.{u}) (yoneda.obj (Spec (spfQuotientOn A I))))
      _ (Scheme.Hom.generate_singleton_mem_propQCTopology (P := @Flat) (Spec.map φ) hflat))
  rw [← Presieve.isSheafFor_iff_generate, Presieve.isSheafFor_singleton] at hsheaf
  obtain ⟨t, ht, -⟩ := hsheaf a hdesc
  refine ⟨ObjectProperty.homMk ((schemeToFormalScheme.map t).hom ≫
    spfQuotientPointOn A (preAdmissibleSpfIndex A hA.1) I), ?_⟩
  have ht' : Spec.map φ ≫ t = a := ht
  refine (Presieve.FamilyOfElements.isAmalgamation_singleton_iff _ _ _).2 ?_
  refine InducedCategory.hom_ext ?_
  exact (schemeToFormalScheme_map_comp_hom_assoc (Spec.map φ) t
    (spfQuotientPointOn A (preAdmissibleSpfIndex A hA.1) I)).symm.trans (by rw [ht', ha])

end Spf

/-! ### Points of a formal scheme descend along fpqc coverings -/

/-- **Descent of points landing in an affine formal chart.** Let `𝔛|_𝔘 ≅ Spf A` be an affine
formal chart of a formal scheme `𝔛`. A compatible family of points of `𝔛` on an fpqc covering
sieve, all of whose members land in `𝔘`, has an amalgamation: the family factors through
`𝔛|_𝔘 ≅ Spf A`, the inclusion of `𝔘` being a monomorphism, and the functor of points of `Spf A`
is an fpqc sheaf by `AlgebraicGeometry.isSheaf_fpqcTopology_formalSchemePoints_spfFormalScheme`. -/
theorem exists_isAmalgamation_of_range_subset_chart {X : FormalScheme.{u}} (U : Opens X.obj)
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : IsAdmissible A) (χ : X.obj.restrict U ≅ spfLTRS A hA.1)
    {T : Scheme.{u}} {S : Sieve T} (hS : S ∈ Scheme.fpqcTopology.{u} T)
    {x : Presieve.FamilyOfElements (formalSchemePoints X) S.arrows} (hx : x.Compatible)
    (hrange : ∀ ⦃Z : Scheme.{u}⦄ (f : Z ⟶ T) (hf : S f),
      Set.range (x f hf).hom.toHom.base ⊆ Set.range (X.obj.ofRestrict U).toHom.base) :
    ∃ t, x.IsAmalgamation t := by
  let ι : spfFormalScheme A hA ⟶ X := ObjectProperty.homMk (χ.inv ≫ X.obj.ofRestrict U)
  let y : Presieve.FamilyOfElements (formalSchemePoints (spfFormalScheme A hA)) S.arrows :=
    fun _ f hf => ObjectProperty.homMk (liftToRestrict U (x f hf).hom (hrange f hf) ≫ χ.hom)
  have hyι : ∀ ⦃Z : Scheme.{u}⦄ (f : Z ⟶ T) (hf : S f), y f hf ≫ ι = x f hf := fun Z f hf =>
    InducedCategory.hom_ext (by
      show (liftToRestrict U (x f hf).hom (hrange f hf) ≫ χ.hom) ≫ χ.inv ≫ X.obj.ofRestrict U
        = (x f hf).hom
      rw [Category.assoc, Iso.hom_inv_id_assoc, liftToRestrict_comp_ofRestrict])
  have hcancel : ∀ {W : Scheme.{u}} (a b : schemeToFormalScheme.obj W ⟶ spfFormalScheme A hA),
      a ≫ ι = b ≫ ι → a = b := by
    intro W a b h
    have h' := congrArg (fun m : schemeToFormalScheme.obj W ⟶ X => m.hom) h
    change a.hom ≫ χ.inv ≫ X.obj.ofRestrict U = b.hom ≫ χ.inv ≫ X.obj.ofRestrict U at h'
    have h'' : (a.hom ≫ χ.inv) ≫ X.obj.ofRestrict U = (b.hom ≫ χ.inv) ≫ X.obj.ofRestrict U :=
      (Category.assoc _ _ _).trans (h'.trans (Category.assoc _ _ _).symm)
    have hmono : Mono (X.obj.toPresheafedSpace.ofRestrict U.isOpenEmbedding) :=
      PresheafedSpace.ofRestrict_mono _ _ _
    have h2 : (a.hom ≫ χ.inv).toHom = (b.hom ≫ χ.inv).toHom :=
      (cancel_mono (X.obj.toPresheafedSpace.ofRestrict U.isOpenEmbedding)).1
        (congrArg LocallyTopologicallyRingedSpace.Hom.toHom h'')
    exact InducedCategory.hom_ext
      ((cancel_mono χ.inv).1 (LocallyTopologicallyRingedSpace.Hom.ext' h2))
  have hy : y.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ comm
    apply hcancel
    show (schemeToFormalScheme.map g₁ ≫ y f₁ h₁) ≫ ι =
      (schemeToFormalScheme.map g₂ ≫ y f₂ h₂) ≫ ι
    rw [Category.assoc, Category.assoc, hyι, hyι]
    exact hx g₁ g₂ h₁ h₂ comm
  obtain ⟨(s : schemeToFormalScheme.obj T ⟶ spfFormalScheme A hA), hs, -⟩ :=
    isSheaf_fpqcTopology_formalSchemePoints_spfFormalScheme A hA S hS y hy
  refine ⟨s ≫ ι, fun Z f hf => ?_⟩
  have hsf : schemeToFormalScheme.map f ≫ s = y f hf := hs f hf
  show schemeToFormalScheme.map f ≫ s ≫ ι = x f hf
  rw [← Category.assoc, hsf, hyι]

/-- The functor of points of a formal scheme `𝔛`, on the category of all schemes, satisfies the
sheaf condition for fpqc coverings. -/
theorem isSheaf_fpqcTopology_formalSchemePoints (X : FormalScheme.{u}) :
    Presieve.IsSheaf Scheme.fpqcTopology.{u} (formalSchemePoints X) := by
  intro T S hS
  refine (isSeparated_fpqcTopology_formalSchemePoints X S hS).isSheafFor fun x hx => ?_
  let z : Presieve.FamilyOfElements (continuousMapPresheaf (T := X.obj)) S.arrows :=
    fun _ f hf => (x f hf).hom.toHom.base.hom
  have hz : z.Compatible := fun Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ comm =>
    congrArg (fun m : schemeToFormalScheme.obj Z ⟶ X => m.hom.toHom.base.hom)
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
  refine Presieve.exists_isAmalgamation_of_locally (isSheaf_zariskiTopology_formalSchemePoints X)
    (isSeparated_fpqcTopology_formalSchemePoints X) hS hx
    (Precoverage.generate_mem_toGrothendieck (T.openCoverOfIsOpenCover V hV).mem₀) ?_
  rintro Y h ⟨W, k, _, ⟨p⟩, rfl⟩
  have := hlin (g p)
  refine exists_isAmalgamation_of_range_subset_chart (U (g p)) (A (g p)).α (hdata (g p)).1
    (ltrsIsoOfPresheafedSpaceIso (hdata (g p)).2.some)
    (Scheme.fpqcTopology.pullback_stable _ hS) (hx.pullback _) ?_
  rintro Z f hf _ ⟨w, rfl⟩
  refine ⟨⟨_, ?_⟩, rfl⟩
  have hw' : (x _ hf).hom.toHom.base w = g ((f ≫ k ≫ (T.openCoverOfIsOpenCover V hV).f p) w) :=
    (congrArg (fun c : C(Z, X.obj) => c w) (hg _ hf)).symm
  show (x _ hf).hom.toHom.base w ∈ U (g p)
  rw [hw']
  exact ((f ≫ k).base w).2

/-- **Stacks 0AI2** for the functor of points of Stacks 0AI1, on the schemes of size below `κ`:
it satisfies the sheaf condition for every family of morphisms of `Sch_κ` which is an fpqc
covering.

Members of `Sch_κ` have their fibre products in `Sch_κ`
(`AlgebraicGeometry.Scheme.size_pullback_lt`), so a family of points compatible on `Sch_κ` is
compatible on all schemes, and `AlgebraicGeometry.isSheaf_fpqcTopology_formalSchemePoints`
applies. -/
@[stacks 0AI2]
theorem isSheafFor_formalSchemeFunctorOfPoints {κ : Cardinal.{u}} (X : FormalScheme.{u})
    {T : (schemeCutoff κ).FullSubcategory} {R : Presieve T}
    (covering : R ∈ Scheme.fpqcPrecoverage.{u}.comap (schemeCutoff κ).ι T) :
    Presieve.IsSheafFor ((formalSchemeFunctorOfPoints κ).obj X) R := by
  obtain ⟨J, S, u, rfl⟩ := R.exists_eq_ofArrows
  rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows] at covering
  simp only [ObjectProperty.ι_obj, ObjectProperty.ι_map] at covering
  have hsheaf : Presieve.IsSheafFor (formalSchemePoints X)
      (Presieve.ofArrows (fun j => (S j).obj) fun j => (u j).hom) := by
    rw [Presieve.isSheafFor_iff_generate]
    exact isSheaf_fpqcTopology_formalSchemePoints X _
      (Precoverage.generate_mem_toGrothendieck covering)
  rw [Presieve.isSheafFor_arrows_iff] at hsheaf ⊢
  intro x hx
  refine hsheaf x fun i j Z gi gj hij => ?_
  let P : (schemeCutoff κ).FullSubcategory :=
    ⟨pullback (u i).hom (u j).hom, Scheme.size_pullback_lt _ _ (S i).property (S j).property⟩
  let xi : schemeToFormalScheme.obj (S i).obj ⟶ X := x i
  let xj : schemeToFormalScheme.obj (S j).obj ⟶ X := x j
  have hP' : schemeToFormalScheme.map (pullback.fst (u i).hom (u j).hom) ≫ xi =
      schemeToFormalScheme.map (pullback.snd (u i).hom (u j).hom) ≫ xj :=
    hx i j P (ObjectProperty.homMk (pullback.fst _ _)) (ObjectProperty.homMk (pullback.snd _ _))
      (InducedCategory.hom_ext pullback.condition)
  show schemeToFormalScheme.map gi ≫ xi = schemeToFormalScheme.map gj ≫ xj
  have := congrArg (schemeToFormalScheme.map (pullback.lift gi gj hij) ≫ ·) hP'
  simpa only [Category.assoc, ← Functor.map_comp_assoc, pullback.lift_fst, pullback.lift_snd]
    using this

end AlgebraicGeometry

end
