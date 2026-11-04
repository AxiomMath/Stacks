module

public import Mathlib.RingTheory.Adjoin.FG
public import Mathlib.RingTheory.FiniteType
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothScheme
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStageDescent
public import StacksFrontier.AlgebraicGeometry.Thickenings
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# Descending a square-zero thickening to a finite type base

Let `Λ` be a ring, let `R` be a `Λ`-algebra and let `I ⊆ R` be an ideal of square zero such
that `R ⧸ I` is of finite type over `Λ`. The finite type `Λ`-subalgebras `A ⊆ R` whose image
in `R ⧸ I` is everything form a directed system whose union is `R`, so `Spec R` is the inverse
limit of the affine schemes `Spec A`. For a limit preserving category fibred in groupoids over
the big fppf site of `S` this means that an object over `Spec R` already lives over one of the
`Spec A`; and for such an `A` the morphism `Spec (R ⧸ I) ⟶ Spec A` is a first order thickening,
because the kernel of `A ⟶ R ⧸ I` is `A ∩ I`.

This is the step of the proof of Stacks 0G2K which says that the thickening produced by
Stacks 0G2J comes from a finite type `Λ`-algebra, and that the original scheme sits inside the
spectrum of that algebra as a first order thickening.

## Main definitions

* `Deformation.Artin.FiniteTypeCover` — the directed index set of finite type `Λ`-subalgebras
  of `R` surjecting onto `R ⧸ I`.
* `Deformation.Artin.specSiteHom` — a compatible morphism of affine spectra, read as a
  morphism of the big fppf category over `S`.

## Main results

* `Deformation.Artin.exists_fg_le_surjective_quotient` — a finite type subalgebra can be
  enlarged by finitely many elements so as to surject onto a finite type quotient.
* `Deformation.Artin.isFirstOrderThickening_quotient_of_sq_eq_bot` — for a subalgebra
  surjecting onto `R ⧸ I` with `I ^ 2 = ⊥`, the induced closed immersion
  `Spec (R ⧸ I) ⟶ Spec A` is a first order thickening.
* `Deformation.Artin.exists_finiteTypeCover_descent` — the descent itself: an object over
  `Spec R` restricts from an object over `Spec A` for some stage `A`.
* `Deformation.Artin.exists_finiteTypeCover_thickening_descent` — the two combined, in the
  form the proof of Stacks 0G2K uses.

## Implementation notes

Restricting the index set to the subalgebras that *already* surject onto `R ⧸ I` is what makes
the enlargement step of the source disappear: these form a cofinal subsystem of all finite type
subalgebras, still directed and still with union `R`, so the descent lands on a stage with the
required surjectivity built in and no pullback along a further inclusion is needed.

Limit preservation (Stacks 07XL) is used through `Deformation.Artin.descentObj_of_essSurj`,
which turns essential surjectivity of the canonical comparison functor into the descent of a
single object along a cartesian arrow. The index category is the opposite of the poset of
stages; it is cofiltered because that poset is directed and nonempty.

The spectra of the stages lie in the chosen big fppf site because they are of finite type over
`Λ`, whose spectrum is assumed to lie in it (Stacks 000R (9)(b)). That `Spec R` is the limit of
the `Spec A` is the statement that `R` is the colimit of the `A`, transported by the spectrum
functor, which preserves limits.

## References

* [Stacks Project, Tag 0G2K](https://stacks.math.columbia.edu/tag/0G2K)
* [Stacks Project, Tag 0G2J](https://stacks.math.columbia.edu/tag/0G2J)
* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace Deformation.Artin

universe u vX uX

/-! ### Finite type subalgebras surjecting onto a quotient -/

section Subalgebras

variable {Λ R : Type u} [CommRing Λ] [CommRing R] [Algebra Λ R]

/-- A finite type subalgebra of `R` can be enlarged by finitely many elements so that its
image in a finite type quotient `R ⧸ I` is everything. -/
public theorem exists_fg_le_surjective_quotient (I : Ideal R)
    [Algebra.FiniteType Λ (R ⧸ I)] (A : Subalgebra Λ R) (hA : A.FG) :
    ∃ A' : Subalgebra Λ R, A'.FG ∧ A ≤ A' ∧
      ∀ z : R ⧸ I, ∃ a ∈ A', Ideal.Quotient.mk I a = z := by
  classical
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra Λ (R ⧸ I)).FG)
  set g : R ⧸ I → R := Function.surjInv Ideal.Quotient.mk_surjective
  refine ⟨A ⊔ Algebra.adjoin Λ (↑(s.image g) : Set R),
    hA.sup (Subalgebra.fg_adjoin_finset _), le_sup_left, ?_⟩
  have hmap : (⊤ : Subalgebra Λ (R ⧸ I)) ≤
      (A ⊔ Algebra.adjoin Λ (↑(s.image g) : Set R)).map (Ideal.Quotient.mkₐ Λ I) := by
    rw [← hs]
    apply Algebra.adjoin_le
    intro w hw
    refine Subalgebra.mem_map.2 ⟨g w, ?_, Function.surjInv_eq Ideal.Quotient.mk_surjective w⟩
    refine SetLike.le_def.1 le_sup_right (Algebra.subset_adjoin ?_)
    exact Finset.mem_coe.2 (Finset.mem_image_of_mem g (Finset.mem_coe.1 hw))
  exact fun z => Subalgebra.mem_map.1 (hmap (Algebra.mem_top (x := z)))

/-- The ring map from a subalgebra of `R` to the quotient `R ⧸ I`. -/
public abbrev quotientRestrict (I : Ideal R) (A : Subalgebra Λ R) : A →+* R ⧸ I :=
  (Ideal.Quotient.mk I).comp (A.val : A →+* R)

/-- The kernel of `A ⟶ R ⧸ I` has square zero as soon as `I` does: it is `A ∩ I`, and `A`
sits inside `R`. -/
public theorem ker_quotientRestrict_sq_eq_bot {I : Ideal R} (hI : I ^ 2 = ⊥)
    (A : Subalgebra Λ R) : RingHom.ker (quotientRestrict I A) ^ 2 = ⊥ := by
  refine le_antisymm ?_ bot_le
  rw [pow_two]
  refine Ideal.mul_le.2 fun a ha b hb => ?_
  have hmul : (a : R) * (b : R) ∈ I ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul (Ideal.Quotient.eq_zero_iff_mem.1 (RingHom.mem_ker.1 ha))
      (Ideal.Quotient.eq_zero_iff_mem.1 (RingHom.mem_ker.1 hb))
  rw [hI] at hmul
  refine Ideal.mem_bot.2 (Subtype.ext ?_)
  simpa using (Ideal.mem_bot.1 hmul)

/-- **The first order thickening of Stacks 0G2K.** If `I ^ 2 = ⊥` and a subalgebra `A ⊆ R`
surjects onto `R ⧸ I`, then `Spec (R ⧸ I) ⟶ Spec A` is a first order thickening. -/
public theorem isFirstOrderThickening_quotient_of_sq_eq_bot {I : Ideal R} (hI : I ^ 2 = ⊥)
    (A : Subalgebra Λ R) (hsurj : Function.Surjective (quotientRestrict I A)) :
    Stacks.Thickenings.IsFirstOrderThickening
      (Spec.map (CommRingCat.ofHom (quotientRestrict I A))) :=
  Stacks.Smooth.isFirstOrderThickening_specMap
    (CommRingCat.ofHom (quotientRestrict I A)) hsurj
    (ker_quotientRestrict_sq_eq_bot hI A)

/-- The finite type `Λ`-subalgebras of `R` whose image in `R ⧸ I` is everything. They index
the directed system used to descend an object over `Spec R`. -/
public abbrev FiniteTypeCover (Λ : Type u) [CommRing Λ] {R : Type u} [CommRing R]
    [Algebra Λ R] (I : Ideal R) : Type u :=
  {A : Subalgebra Λ R // A.FG ∧ Function.Surjective (quotientRestrict I A)}

variable (I : Ideal R)

/-- A subalgebra surjects onto `R ⧸ I` as soon as a smaller one does. -/
public theorem surjective_quotientRestrict_of_le {A A' : Subalgebra Λ R} (h : A ≤ A')
    (hA : Function.Surjective (quotientRestrict I A)) :
    Function.Surjective (quotientRestrict I A') := by
  intro z
  obtain ⟨a, ha⟩ := hA z
  exact ⟨⟨(a : R), h a.2⟩, ha⟩

/-- A subalgebra surjects onto `R ⧸ I` exactly when every class has a representative in it. -/
public theorem surjective_quotientRestrict_iff (A : Subalgebra Λ R) :
    Function.Surjective (quotientRestrict I A) ↔
      ∀ z : R ⧸ I, ∃ a ∈ A, Ideal.Quotient.mk I a = z := by
  refine ⟨fun h z => ?_, fun h z => ?_⟩
  · obtain ⟨a, ha⟩ := h z
    exact ⟨(a : R), a.2, ha⟩
  · obtain ⟨a, haA, ha⟩ := h z
    exact ⟨⟨a, haA⟩, ha⟩

variable [Algebra.FiniteType Λ (R ⧸ I)]

/-- Some finitely generated subalgebra of `R` surjects onto `R ⧸ I`. -/
public instance : Nonempty (FiniteTypeCover Λ I) := by
  obtain ⟨A', hfg, _, hsurj⟩ :=
    exists_fg_le_surjective_quotient (Λ := Λ) I ⊥ Subalgebra.fg_bot
  exact ⟨⟨A', hfg, (surjective_quotientRestrict_iff I A').2 hsurj⟩⟩

/-- The stages are directed: the join of two stages is a stage. -/
public instance : IsDirected (FiniteTypeCover Λ I) (· ≤ ·) where
  directed a b :=
    ⟨⟨a.1 ⊔ b.1, a.2.1.sup b.2.1,
      surjective_quotientRestrict_of_le I le_sup_left a.2.2⟩,
      Subtype.coe_le_coe.1 le_sup_left, Subtype.coe_le_coe.1 le_sup_right⟩

/-- Every element of `R` lies in some stage. -/
public theorem exists_mem_finiteTypeCover (r : R) :
    ∃ A : FiniteTypeCover Λ I, r ∈ A.1 := by
  obtain ⟨A⟩ : Nonempty (FiniteTypeCover Λ I) := inferInstance
  have hfg : (Algebra.adjoin Λ ({r} : Set R)).FG := by
    simpa using Subalgebra.fg_adjoin_finset (R := Λ) ({r} : Finset R)
  exact ⟨⟨A.1 ⊔ Algebra.adjoin Λ ({r} : Set R), A.2.1.sup hfg,
    surjective_quotientRestrict_of_le I le_sup_left A.2.2⟩,
    SetLike.le_def.1 le_sup_right (Algebra.subset_adjoin rfl)⟩

end Subalgebras

/-! ### Morphisms of affine objects of the site -/

/-- A compatible morphism of affine spectra, read as a morphism of the big fppf category
over `S`. -/
public def specSiteHom (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {R A : Type u} [CommRing R] [CommRing A]
    (hR : B.Contains (Spec (.of R))) (hA : B.Contains (Spec (.of A)))
    (fR : Spec (.of R) ⟶ S) (fA : Spec (.of A) ⟶ S)
    (g : Spec (.of R) ⟶ Spec (.of A)) (hg : g ≫ fA = fR) :
    siteObject B S hS hR fR ⟶ siteObject B S hS hA fA :=
  Over.homMk (ObjectProperty.homMk (X := B.obj hR) (Y := B.obj hA) g)
    (ObjectProperty.hom_ext _ hg)

/-- The underlying morphism of schemes of `specSiteHom` is the given morphism of spectra. -/
public theorem toScheme_specSiteHom (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {R A : Type u} [CommRing R] [CommRing A]
    (hR : B.Contains (Spec (.of R))) (hA : B.Contains (Spec (.of A)))
    (fR : Spec (.of R) ⟶ S) (fA : Spec (.of A) ⟶ S)
    (g : Spec (.of R) ⟶ Spec (.of A)) (hg : g ≫ fA = fR) :
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
      (specSiteHom B S hS hR hA fR fA g hg) = g := rfl

/-! ### The inverse system of the stages -/

section Stages

/-- The structure morphism of a stage over the base. -/
public abbrev stageBase {Λ R : Type u} [CommRing Λ] [CommRing R] [Algebra Λ R]
    {S : Scheme.{u}} (uΛ : Spec (.of Λ) ⟶ S) (A : Subalgebra Λ R) :
    Spec (.of A) ⟶ S :=
  Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ uΛ

/-- A finite type subalgebra of a ring in the site has its spectrum in the site. -/
public theorem contains_stage (B : BigFppfSite.{u}) {Λ R : Type u} [CommRing Λ]
    [CommRing R] [Algebra Λ R] (hΛ : B.Contains (Spec (.of Λ)))
    (A : Subalgebra Λ R) (hA : A.FG) : B.Contains (Spec (.of A)) := by
  have : Algebra.FiniteType Λ A := (Subalgebra.fg_iff_finiteType A).1 hA
  exact Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
    Λ A hΛ

/-- A `Λ`-algebra map is compatible with the structure maps to the base. -/
private theorem spec_map_comp_stageBase {Λ A B : Type u} [CommRing Λ] [CommRing A] [CommRing B]
    [Algebra Λ A] [Algebra Λ B] {S : Scheme.{u}} (uΛ : Spec (.of Λ) ⟶ S) (f : A →ₐ[Λ] B) :
    Spec.map (CommRingCat.ofHom (f : A →+* B)) ≫ Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫
      uΛ = Spec.map (CommRingCat.ofHom (algebraMap Λ B)) ≫ uΛ := by
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap]

/-- The inclusion of a stage into `Spec R` is a morphism over the base. -/
public theorem stageBase_val {Λ R : Type u} [CommRing Λ] [CommRing R] [Algebra Λ R]
    {S : Scheme.{u}} (uΛ : Spec (.of Λ) ⟶ S) (A : Subalgebra Λ R) :
    Spec.map (CommRingCat.ofHom (A.val : A →+* R)) ≫ stageBase uΛ A =
      Spec.map (CommRingCat.ofHom (algebraMap Λ R)) ≫ uΛ := by
  exact spec_map_comp_stageBase uΛ _

/-- The transitions of the inverse system are morphisms over the base. -/
public theorem stageBase_inclusion {Λ R : Type u} [CommRing Λ] [CommRing R] [Algebra Λ R]
    {S : Scheme.{u}} (uΛ : Spec (.of Λ) ⟶ S) {A A' : Subalgebra Λ R} (h : A ≤ A') :
    Spec.map (CommRingCat.ofHom ((Subalgebra.inclusion h : A →ₐ[Λ] A') : A →+* A')) ≫
        stageBase uΛ A = stageBase uΛ A' := by
  exact spec_map_comp_stageBase uΛ _

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Λ R : Type u} [CommRing Λ] [CommRing R] [Algebra Λ R]
  (uΛ : Spec (.of Λ) ⟶ S) (hΛ : B.Contains (Spec (.of Λ))) (I : Ideal R)

/-- A stage of the inverse system, as an affine object of the site over `S`. -/
public def stage (A : FiniteTypeCover Λ I) : AlgebraicGeometry.BigAffineFppf B S hS :=
  ⟨siteObject B S hS (contains_stage B hΛ A.1 A.2.1) (stageBase uΛ A.1),
    inferInstanceAs (IsAffine (Spec (.of A.1)))⟩

/-- The transition morphism of the inverse system attached to an inclusion of stages. -/
public def stageMap {i j : (FiniteTypeCover Λ I)ᵒᵖ} (a : i ⟶ j) :
    stage B S hS uΛ hΛ I i.unop ⟶ stage B S hS uΛ hΛ I j.unop :=
  ObjectProperty.homMk
    (specSiteHom B S hS (contains_stage B hΛ i.unop.1 i.unop.2.1)
      (contains_stage B hΛ j.unop.1 j.unop.2.1)
      (stageBase uΛ i.unop.1) (stageBase uΛ j.unop.1)
      (Spec.map (CommRingCat.ofHom
        ((Subalgebra.inclusion (leOfHom a.unop) : j.unop.1 →ₐ[Λ] i.unop.1) :
          j.unop.1 →+* i.unop.1)))
      (stageBase_inclusion uΛ (leOfHom a.unop)))

/-- The cofiltered diagram of stages. -/
public def stageDiagram :
    (FiniteTypeCover Λ I)ᵒᵖ ⥤ AlgebraicGeometry.BigAffineFppf B S hS where
  obj i := stage B S hS uΛ hΛ I i.unop
  map a := stageMap B S hS uΛ hΛ I a
  map_id i := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    change Spec.map (CommRingCat.ofHom (RingHom.id i.unop.1)) = 𝟙 _
    simp
  map_comp {i j k} a b := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    change Spec.map (CommRingCat.ofHom
        ((Subalgebra.inclusion (leOfHom (a ≫ b).unop) : k.unop.1 →ₐ[Λ] i.unop.1) :
          k.unop.1 →+* i.unop.1)) =
      Spec.map (CommRingCat.ofHom
        ((Subalgebra.inclusion (leOfHom a.unop) : j.unop.1 →ₐ[Λ] i.unop.1) :
          j.unop.1 →+* i.unop.1)) ≫
      Spec.map (CommRingCat.ofHom
        ((Subalgebra.inclusion (leOfHom b.unop) : k.unop.1 →ₐ[Λ] j.unop.1) :
          k.unop.1 →+* j.unop.1))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1

variable (hR : B.Contains (Spec (.of R)))

/-- The cone over the diagram of stages with vertex `Spec R`. -/
public def stageCone : Cone (stageDiagram B S hS uΛ hΛ I) where
  pt := ⟨siteObject B S hS hR (Spec.map (CommRingCat.ofHom (algebraMap Λ R)) ≫ uΛ),
    inferInstanceAs (IsAffine (Spec (.of R)))⟩
  π :=
    { app := fun i =>
        ObjectProperty.homMk
          (specSiteHom B S hS hR (contains_stage B hΛ i.unop.1 i.unop.2.1)
            (Spec.map (CommRingCat.ofHom (algebraMap Λ R)) ≫ uΛ)
            (stageBase uΛ i.unop.1)
            (Spec.map (CommRingCat.ofHom ((i.unop.1).val : i.unop.1 →+* R)))
            (stageBase_val uΛ i.unop.1))
      naturality := by
        intro i j a
        apply ObjectProperty.hom_ext
        apply Over.OverMorphism.ext
        apply ObjectProperty.hom_ext
        change Spec.map (CommRingCat.ofHom ((j.unop.1).val : j.unop.1 →+* R)) ≫ 𝟙 _ =
          Spec.map (CommRingCat.ofHom ((i.unop.1).val : i.unop.1 →+* R)) ≫
            Spec.map (CommRingCat.ofHom
              ((Subalgebra.inclusion (leOfHom a.unop) : j.unop.1 →ₐ[Λ] i.unop.1) :
                j.unop.1 →+* i.unop.1))
        rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        congr 1 }

/-- The diagram of the rings of the stages. -/
public def stageRingDiagram : FiniteTypeCover Λ I ⥤ CommRingCat.{u} where
  obj A := CommRingCat.of A.1
  map {i j} a := CommRingCat.ofHom
    ((Subalgebra.inclusion (leOfHom a) : i.1 →ₐ[Λ] j.1) : i.1 →+* j.1)
  map_id i := by
    ext z
    rfl
  map_comp {i j k} a b := by
    ext z
    rfl

/-- The cocone of the rings of the stages with vertex `R`. -/
public def stageRingCocone : Cocone (stageRingDiagram (Λ := Λ) I) where
  pt := CommRingCat.of R
  ι :=
    { app := fun A => CommRingCat.ofHom ((A.1).val : A.1 →+* R)
      naturality := by
        intro i j a
        ext z
        rfl }

variable [Algebra.FiniteType Λ (R ⧸ I)]

/-- `R` is the directed colimit of the stages. -/
public def isColimitStageRingCocone : IsColimit (stageRingCocone (Λ := Λ) I) := by
  have := reflectsColimit_of_reflectsIsomorphisms (stageRingDiagram (Λ := Λ) I)
    (forget CommRingCat)
  apply isColimitOfReflects (forget CommRingCat)
  apply Types.FilteredColimit.isColimitOf'
  · intro z
    obtain ⟨A, hz⟩ := exists_mem_finiteTypeCover (Λ := Λ) I z
    exact ⟨A, ⟨z, hz⟩, rfl⟩
  · intro i a b hab
    exact ⟨i, 𝟙 i, congrArg _ (Subtype.ext hab)⟩

/-- `Spec R` is the inverse limit of the spectra of the stages. -/
public def isLimitStageCone :
    IsLimit ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).mapCone
      (stageCone B S hS uΛ hΛ I hR)) :=
  isLimitOfPreserves Scheme.Spec (isColimitStageRingCocone (Λ := Λ) I).op

end Stages

/-! ### The descent -/

/-- **The descent step of Stacks 0G2K.** Let `𝒳` be a limit preserving category fibred in
groupoids over the big fppf site of `S`, let `R` be a `Λ`-algebra whose spectrum lies in the
site, and let `I ⊆ R` be an ideal with `R ⧸ I` of finite type over `Λ`. Then every object of
`𝒳` over `Spec R` is the restriction of an object over `Spec A` for some finite type
`Λ`-subalgebra `A ⊆ R` which surjects onto `R ⧸ I`. -/
public theorem exists_finiteTypeCover_descent
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, vX, u + 1, uX} (AlgebraicGeometry.BigFppfOver B S hS))
    (hlim : IsLimitPreserving.{u, u, u, uX, vX} B S hS 𝒳)
    {Λ R : Type u} [CommRing Λ] [CommRing R] [Algebra Λ R]
    (uΛ : Spec (.of Λ) ⟶ S) (hΛ : B.Contains (Spec (.of Λ)))
    (hR : B.Contains (Spec (.of R)))
    (I : Ideal R) [Algebra.FiniteType Λ (R ⧸ I)]
    (y : 𝒳.val.p.Fiber (siteObject B S hS hR
      (Spec.map (CommRingCat.ofHom (algebraMap Λ R)) ≫ uΛ))) :
    ∃ (A : FiniteTypeCover Λ I)
      (x' : 𝒳.val.p.Fiber
        (siteObject B S hS (contains_stage B hΛ A.1 A.2.1) (stageBase uΛ A.1)))
      (δ : y.1 ⟶ x'.1),
      𝒳.val.p.IsHomLift
        (specSiteHom B S hS hR (contains_stage B hΛ A.1 A.2.1)
          (Spec.map (CommRingCat.ofHom (algebraMap Λ R)) ≫ uΛ) (stageBase uΛ A.1)
          (Spec.map (CommRingCat.ofHom ((A.1).val : A.1 →+* R)))
          (stageBase_val uΛ A.1)) δ := by
  have : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  have : (colimitComparison 𝒳.val.p
      (stageDiagram B S hS uΛ hΛ I ⋙ AlgebraicGeometry.BigAffineFppf.inclusion B S hS)
      ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).mapCone
        (stageCone B S hS uΛ hΛ I hR))).IsEquivalence :=
    hlim ((FiniteTypeCover Λ I)ᵒᵖ) (stageDiagram B S hS uΛ hΛ I)
      (stageCone B S hS uΛ hΛ I hR) (isLimitStageCone B S hS uΛ hΛ I hR)
  obtain ⟨i, xi, δ, hδ⟩ :=
    descentObj_of_essSurj 𝒳.val.p
      (stageDiagram B S hS uΛ hΛ I ⋙ AlgebraicGeometry.BigAffineFppf.inclusion B S hS)
      ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).mapCone
        (stageCone B S hS uΛ hΛ I hR)) y
  exact ⟨i.unop, xi, δ, hδ⟩

/-- **The descent step of Stacks 0G2K, with its thickening.** In the situation of
`Deformation.Artin.exists_finiteTypeCover_descent`, if moreover `I ^ 2 = ⊥` then
`Spec (R ⧸ I) ⟶ Spec A` is a first order thickening. -/
public theorem exists_finiteTypeCover_thickening_descent
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, vX, u + 1, uX} (AlgebraicGeometry.BigFppfOver B S hS))
    (hlim : IsLimitPreserving.{u, u, u, uX, vX} B S hS 𝒳)
    {Λ R : Type u} [CommRing Λ] [CommRing R] [Algebra Λ R]
    (uΛ : Spec (.of Λ) ⟶ S) (hΛ : B.Contains (Spec (.of Λ)))
    (hR : B.Contains (Spec (.of R)))
    (I : Ideal R) (hI : I ^ 2 = ⊥) [Algebra.FiniteType Λ (R ⧸ I)]
    (y : 𝒳.val.p.Fiber (siteObject B S hS hR
      (Spec.map (CommRingCat.ofHom (algebraMap Λ R)) ≫ uΛ))) :
    ∃ (A : FiniteTypeCover Λ I)
      (x' : 𝒳.val.p.Fiber
        (siteObject B S hS (contains_stage B hΛ A.1 A.2.1) (stageBase uΛ A.1)))
      (δ : y.1 ⟶ x'.1),
      𝒳.val.p.IsHomLift
        (specSiteHom B S hS hR (contains_stage B hΛ A.1 A.2.1)
          (Spec.map (CommRingCat.ofHom (algebraMap Λ R)) ≫ uΛ) (stageBase uΛ A.1)
          (Spec.map (CommRingCat.ofHom ((A.1).val : A.1 →+* R)))
          (stageBase_val uΛ A.1)) δ ∧
      Stacks.Thickenings.IsFirstOrderThickening
        (Spec.map (CommRingCat.ofHom (quotientRestrict I A.1))) := by
  obtain ⟨A, x', δ, hδ⟩ :=
    exists_finiteTypeCover_descent B S hS 𝒳 hlim uΛ hΛ hR I y
  exact ⟨A, x', δ, hδ, isFirstOrderThickening_quotient_of_sq_eq_bot hI A.1 A.2.2⟩

end Deformation.Artin

end
