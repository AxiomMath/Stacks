module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.DegreeOneConnectingMorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.SliceComplexExtClass
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.SpectralSequenceHypothesis
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0A6G: first Čech cohomology and torsors, through the bijection of Stacks 03AJ

Let `(C, K)` be a site, `G` an abelian sheaf on `C` and `𝒰 = {U_i → U}` a covering family. The
first cohomology `H¹(U, G)` enters twice: as the target of the comparison
`Ȟ¹(𝒰, G) → H¹(U, G)` of Stacks 03AX, read in the right derived sections functor, and as the
group `Sheaf.H (G.over U) 1` of the bijection of Stacks 03AJ with the isomorphism classes of
`G|_U`-torsors. The two are identified by the canonical isomorphism of universal `δ`-functors
`Stacks.Cohomology.Torsors.rightDerivedSectionsOneEquivSliceH`.

The class of a torsor which is trivial over every `U_i` under the bijection of 03AJ is the image
of its Čech class under the comparison of 03AX. The proof is that of the source: embed `G` in an
injective sheaf `I` with quotient `Q`; the Čech cocycle of the torsor is the Čech coboundary of a
degree-zero cochain of `I`, whose image glues to a section `q` of `Q` over `U`. The comparison
sends the Čech class to the connecting image of `q`
(`Stacks.CechSite.cechCohomologyToCohomology_one_cls_eq_rightDerivedPlusδ`), the identification
of the two models carries it to the extension class of `q`
(`Stacks.Cohomology.Torsors.rightDerivedSectionsOneEquivSliceH_δ`), and that is the class of the
torsor of local lifts of `q` (`Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1_cocycleTorsor`),
which is isomorphic to the given torsor because the two have the same Čech class.

## Main results

* `Stacks.CechSite.cechH1ToSliceH`: the comparison `Ȟ¹(𝒰, G) → H¹(U, G)` of Stacks 03AX, with
  values in `Sheaf.H (G.over U) 1`.
* `Stacks.CechSite.torsorIsoClassesEquivH1_eq_cechH1ToSliceH_cechClass`: the class of a torsor
  trivial on the members of `𝒰`, under the bijection of 03AJ, is the image of its Čech class.
* `Stacks.CechSite.cechH1ToSliceH_injective_and_range_eq`: **Stacks 0A6G**.

## References

* [Stacks Project, Tag 0A6G](https://stacks.math.columbia.edu/tag/0A6G)
* [Stacks Project, Tag 03AJ](https://stacks.math.columbia.edu/tag/03AJ)
* [Stacks Project, Tag 03AX](https://stacks.math.columbia.edu/tag/03AX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Cohomology.Torsors

universe a w v u

namespace Stacks.CechSite

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [Category.{v} C] (K : GrothendieckTopology C) {U : C}
  (E : PreZeroHypercover.{w} U)
  [HasProducts.{w} AddCommGrpCat.{max a u v w}]
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun j ↦ Over.mk (E.f (i j)))]
  [HasSheafify K AddCommGrpCat.{max a u v w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max a u v w}]
  [EnoughInjectives (Sheaf K AddCommGrpCat.{max a u v w})]
  [HasSheafify (K.over U) AddCommGrpCat.{max a u v w}]
  [HasExt.{max a u v w} (Sheaf (K.over U) AddCommGrpCat.{max a u v w})]

/-- **The comparison `Ȟ¹(𝒰, G) → H¹(U, G)` of Stacks 03AX, with values in the first cohomology
group of the bijection of Stacks 03AJ.** It is `Stacks.CechSite.cechH1ToCohomology` followed by
the canonical identification `Stacks.Cohomology.Torsors.rightDerivedSectionsOneEquivSliceH` of
the right derived sections with `Sheaf.H (G.over U) 1`. -/
def cechH1ToSliceH (hE : E.sieve₀ ∈ K U) (G : Sheaf K AddCommGrpCat.{max a u v w}) :
    cechH1 E G.obj →+ Sheaf.H (G.over U) 1 :=
  (rightDerivedSectionsOneEquivSliceH.{a, w} K U G).toAddMonoidHom.comp
    (cechH1ToCohomology.{a} K E hE G)

/-- The comparison `Stacks.CechSite.cechH1ToSliceH : Ȟ¹(𝒰, G) → H¹(U, G)` is injective. -/
theorem cechH1ToSliceH_injective (hE : E.sieve₀ ∈ K U) (G : Sheaf K AddCommGrpCat.{max a u v w}) :
    Function.Injective (cechH1ToSliceH.{a} K E hE G) :=
  (rightDerivedSectionsOneEquivSliceH.{a, w} K U G).injective.comp
    (injective_cechH1ToCohomology.{a} K E hE G)

/-- **The bijection of Stacks 03AJ on a torsor trivial over the members of `𝒰` is the image of its
Čech class under the comparison `Ȟ¹(𝒰, G) → H¹(U, G)`.** -/
theorem torsorIsoClassesEquivH1_eq_cechH1ToSliceH_cechClass (hE : E.sieve₀ ∈ K U)
    (G : Sheaf K AddCommGrpCat.{max a u v w}) (c : LocallyTrivialClass E G) :
    torsorIsoClassesEquivH1.{max a u v w} (G.over U) c.1 =
      cechH1ToSliceH.{a} K E hE G (cechClass E G c) := by
  obtain ⟨_, F, rfl, hF⟩ := c
  let s : ∀ i, F.1.presheaf.obj (op (Over.mk (E.f i))) := fun i ↦ Classical.choice (hF i)
  rw [cechClass_mk E G F hF s]
  let S : ShortComplex (Sheaf K AddCommGrpCat.{max a u v w}) :=
    ShortComplex.mk (Injective.ι G) (cokernel.π (Injective.ι G)) (cokernel.condition _)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_cokernel _
      mono_f := Injective.ι_mono G
      epi_g := inferInstance }
  have : Injective S.X₂ := Injective.injective_under G
  let z := transitionCocycle E G F s
  obtain ⟨b, hb⟩ := exists_cechDifferential_zero_of_injective.{a, w, v, u} E S.X₂
    (pushCocycles1 E S.f.hom z)
  obtain ⟨q, hq⟩ := exists_cechAugmentationPre_eq_pushCochain.{a, w, v, u} E hE S z b hb
  have hA := cechCohomologyToCohomology_one_cls_eq_rightDerivedPlusδ.{a} K E hE S hS z b hb q hq
  have hΦ := rightDerivedSectionsOneEquivSliceH_δ.{a, w} K U S hS q
  have hX := mk₀_comp_extClass_map_overPullback_eq.{a, w, v, u} E hE S hS z b hb q hq
  have hT := torsorIsoClassesEquivH1_cocycleTorsor.{max a u v w} E S hS hE z b hb
  let T := cocycleTorsor E S hS hE z b hb
  have hiso : Quotient.mk (torsorSetoid (G.over U)) F = Quotient.mk (torsorSetoid (G.over U)) T :=
    congrArg Subtype.val (cechClass_injective E G hE
      (a₁ := ⟨Quotient.mk (torsorSetoid (G.over U)) F, F, rfl, hF⟩)
      (a₂ := ⟨Quotient.mk (torsorSetoid (G.over U)) T, T, rfl,
        fun i ↦ ⟨cocycleSection E S hS hE z b hb i⟩⟩)
      ((cechClass_mk E G F hF s).trans (cechClass_cocycleTorsor E S hS hE _ b hb).symm))
  exact (congrArg (torsorIsoClassesEquivH1.{max a u v w} (G.over U)) hiso).trans
    (hT.trans (hX.symm.trans (hΦ.symm.trans
      (congrArg (rightDerivedSectionsOneEquivSliceH.{a, w} K U G) hA.symm))))

/-- **Stacks 0A6G with the sheafification, injectives and `Ext` instances as parameters**; the
registered form, `Stacks.CechSite.cechH1ToSliceH_injective_and_range_eq`, constructs them. -/
theorem injective_cechH1ToSliceH_and_range_eq (hE : E.sieve₀ ∈ K U)
    (G : Sheaf K AddCommGrpCat.{max a u v w}) :
    Function.Injective (cechH1ToSliceH.{a} K E hE G) ∧
      (∀ c : LocallyTrivialClass E G,
        cechH1ToSliceH.{a} K E hE G (cechClass E G c) =
          torsorIsoClassesEquivH1.{max a u v w} (G.over U) c.1) ∧
      Set.range (cechH1ToSliceH.{a} K E hE G) =
        torsorIsoClassesEquivH1.{max a u v w} (G.over U) ''
          {c | ∃ F : AbelianTorsor (G.over U),
            Quotient.mk (torsorSetoid (G.over U)) F = c ∧ IsTrivialOnMembers E G F} := by
  refine ⟨cechH1ToSliceH_injective.{a} K E hE G,
    fun c ↦ (torsorIsoClassesEquivH1_eq_cechH1ToSliceH_cechClass.{a} K E hE G c).symm, ?_⟩
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨c, rfl⟩ := cechClass_surjective.{a, w, v, u} E hE G x
    obtain ⟨F, hFc, hF⟩ := c.2
    exact ⟨c.1, ⟨F, hFc, (isTrivialOnMembers_iff E G F).2 hF⟩,
      torsorIsoClassesEquivH1_eq_cechH1ToSliceH_cechClass.{a} K E hE G c⟩
  · rintro ⟨_, ⟨F, rfl, hF⟩, rfl⟩
    exact ⟨cechClass E G ⟨_, F, rfl, (isTrivialOnMembers_iff E G F).1 hF⟩,
      (torsorIsoClassesEquivH1_eq_cechH1ToSliceH_cechClass.{a} K E hE G _).symm⟩

end Stacks.CechSite

namespace Stacks.CechSite

open Stacks.Cohomology.SiteModules

variable {C : Type u} [Category.{v} C] (K : GrothendieckTopology C) {U : C}
  (E : PreZeroHypercover.{w} U)
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun j ↦ Over.mk (E.f (i j)))]

/-- Let `𝒰 = {U_i → U}` be a covering of a site and `G` an abelian sheaf. The map
`Ȟ¹(𝒰, G) → H¹(U, G)` of Stacks 03AX is injective and, through the bijection of Stacks 03AJ between
isomorphism classes of `G|_U`-torsors and `H¹(U, G)`, identifies `Ȟ¹(𝒰, G)` with the set of
isomorphism classes of `G|_U`-torsors which restrict to trivial torsors over each `U_i`: the class
under 03AJ of such a torsor is the image of its Čech class, and the image of `Ȟ¹(𝒰, G)` is exactly
the set of these classes.

Here `H¹(U, G)` is `Sheaf.H (G.over U) 1`, the target of the bijection of 03AJ, and the map is the
comparison of 03AX read there through the canonical identification of the two models of first
cohomology (`Stacks.CechSite.cechH1ToSliceH`). Sheafification, the comparison of the sheaf
topology with local bijectivity, enough injectives and the `Ext`-groups at the coefficient
universe `max a u v w` exist on every site and are constructed in the statement. The existence
of the iterated fibre products of the members of `𝒰` is part of the definition of a covering in
the source. -/
@[stacks 0A6G]
theorem cechH1ToSliceH_injective_and_range_eq (hE : E.sieve₀ ∈ K U)
    (G : Sheaf K AddCommGrpCat.{max a u v w}) :
    letI : HasSheafify K AddCommGrpCat.{max a u v w} :=
      site_hasSheafify_addCommGrp.{u, v, max a w}
    letI : K.WEqualsLocallyBijective AddCommGrpCat.{max a u v w} :=
      site_wEqualsLocallyBijective_addCommGrp.{u, v, max a w}
    letI : EnoughInjectives (Sheaf K AddCommGrpCat.{max a u v w}) :=
      CategoryTheory.Sheaf.enoughInjectives_addCommGrpCat_max.{max a w, v, u} K
    letI : HasSheafify (K.over U) AddCommGrpCat.{max a u v w} :=
      site_hasSheafify_addCommGrp.{max u v, v, max a w}
    letI : EnoughInjectives (Sheaf (K.over U) AddCommGrpCat.{max a u v w}) :=
      CategoryTheory.Sheaf.enoughInjectives_addCommGrpCat_max.{max a w, v, max u v} (K.over U)
    letI : HasExt.{max a u v w} (Sheaf (K.over U) AddCommGrpCat.{max a u v w}) :=
      hasExt_of_enoughInjectives _
    Function.Injective (cechH1ToSliceH.{a} K E hE G) ∧
      (∀ c : LocallyTrivialClass E G,
        cechH1ToSliceH.{a} K E hE G (cechClass E G c) =
          torsorIsoClassesEquivH1.{max a u v w} (G.over U) c.1) ∧
      Set.range (cechH1ToSliceH.{a} K E hE G) =
        torsorIsoClassesEquivH1.{max a u v w} (G.over U) ''
          {c | ∃ F : AbelianTorsor (G.over U),
            Quotient.mk (torsorSetoid (G.over U)) F = c ∧ IsTrivialOnMembers E G F} := by
  let : HasSheafify K AddCommGrpCat.{max a u v w} :=
    site_hasSheafify_addCommGrp.{u, v, max a w}
  let : K.WEqualsLocallyBijective AddCommGrpCat.{max a u v w} :=
    site_wEqualsLocallyBijective_addCommGrp.{u, v, max a w}
  let : EnoughInjectives (Sheaf K AddCommGrpCat.{max a u v w}) :=
    CategoryTheory.Sheaf.enoughInjectives_addCommGrpCat_max.{max a w, v, u} K
  let : HasSheafify (K.over U) AddCommGrpCat.{max a u v w} :=
    site_hasSheafify_addCommGrp.{max u v, v, max a w}
  let : EnoughInjectives (Sheaf (K.over U) AddCommGrpCat.{max a u v w}) :=
    CategoryTheory.Sheaf.enoughInjectives_addCommGrpCat_max.{max a w, v, max u v} (K.over U)
  let : HasExt.{max a u v w} (Sheaf (K.over U) AddCommGrpCat.{max a u v w}) :=
    hasExt_of_enoughInjectives _
  let : HasExt.{max a u v w} (Sheaf K AddCommGrpCat.{max a u v w}) :=
    hasExt_of_enoughInjectives _
  exact injective_cechH1ToSliceH_and_range_eq.{a} K E hE G

end Stacks.CechSite

end
