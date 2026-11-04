module

public import StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.OpenImmersion
import StacksCore.Tactic.StacksAttribute

/-!
# A left inverse splits the second arrow of the conormal sequence

For an immersion `i : Z ⟶ X` of schemes over `S`, [Stacks, Tag 0474] asserts that the canonical
sequence `0 ⟶ 𝒞_{Z/X} ⟶ i^*Ω_{X/S} ⟶ Ω_{Z/S} ⟶ 0` of [Stacks, Tag 01UZ] is *(locally) split
exact* when `i` *(locally) has a left inverse*, and that for a section `s : S ⟶ X` of `X ⟶ S` the
first arrow `𝒞_{S/X} ⟶ s^*Ω_{X/S}` is an isomorphism.

This file proves the splitting of the *second* arrow, which is the step the source's proof
performs with `i^*c_g`: if `g : X ⟶ Z` is a left inverse of `i` over `S`, then
`i^*Ω_{X/S} ⟶ Ω_{Z/S}` is a split epimorphism, globally if `g` is global and over an open
neighbourhood of every point of `Z` if `g` is only local.

## Main results

All names are in the namespace `Stacks.ConormalSequenceSplit`.

* `isSplitEpi_relativeDifferentialsMap_of_retraction`: the canonical map `i^*Ω_{X/S} ⟶ Ω_{Z/S}` of
  [Stacks, Tag 01UV] is a split epimorphism as soon as `i` has a left inverse over `S`. No
  hypothesis on `i` is used.
* `isSplitEpi_differentialsMapOver_of_retraction`: the same for an immersion, which is the
  hypothesis [Stacks, Tag 0474] states it under. This is the assertion labelled *a left inverse
  splits the second arrow*.
* `isSplitEpi_relativeDifferentialsMap_restrict_of_localRetraction`: the restriction of that map to
  an open `V` of `Z` on which `i` admits a left inverse is a split epimorphism.
* `isSplitEpi_differentialsMapOver_restrictFunctor_of_localRetraction`: the same statement for
  `AlgebraicGeometry.Scheme.Modules.restrictFunctor V.ι` in place of the inverse image along `V.ι`,
  which is the spelling the splitting of the restricted three-term sequence consumes.
* `forall_exists_isSplitEpi_restrict_of_localRetraction`: hence, if `i` locally has a left inverse
  over `S`, the map is split over a neighbourhood of every point of `Z`. This is the assertion
  labelled *a local left inverse locally splits the second arrow*.
* `isSplitEpi_relativeDifferentialsMap_of_section`: a section of `X ⟶ S` is an immersion with a
  left inverse over `S`, namely `X ⟶ S` itself, so its second arrow is split. This is the
  hypothesis half of the source's final assertion.

## Route

Everything rests on the functoriality of [Stacks, Tag 01UV] in the *source* morphism, which is
`AlgebraicGeometry.Scheme.Hom.IsRelativeDifferentialsMap.comp`, together with its two companions
`AlgebraicGeometry.Scheme.Hom.IsRelativeDifferentialsMap.congr_left` and
`AlgebraicGeometry.Scheme.Hom.isRelativeDifferentialsMap_id`, and on the uniqueness
`AlgebraicGeometry.Scheme.Hom.IsRelativeDifferentialsMap.unique` of the canonical map.

Write `q : Z ⟶ S` for the structure morphism of `Z`, `b : i^*Ω_{X/S} ⟶ Ω_{Z/S}` for the canonical
map of `i` and `c : g^*Ω_{Z/S} ⟶ Ω_{X/S}` for the canonical map of a left inverse `g` — the
source's `c_g`. Composition of canonical maps in the source direction identifies
`i^*c ∘ b` with the canonical map of `i ≫ g`; transporting along `i ≫ g = 𝟙 Z` and using that
the canonical map of an identity is the comparison isomorphism `(𝟙 Z)^*Ω_{Z/S} ≅ Ω_{Z/S}`, the
composite `Ω_{Z/S} ≅ (𝟙 Z)^*Ω_{Z/S} ≅ i^*g^*Ω_{Z/S} ⟶ i^*Ω_{X/S}` is a right inverse of `b`.
That is the source's "`i^*c_g` gives a right inverse", and no affine chart is used.

For the local statement the same argument is run for the restricted morphism `j : V ⟶ U`, and the
canonical map of `V ↪ Z ↪ X` is computed twice by the same composition law: once through `U` and
once through `Z`. The two factors that are not `b` are isomorphisms — the pullback comparison
isomorphisms and, by
`AlgebraicGeometry.Scheme.Hom.isIso_relativeDifferentialsMap_id_base`, the canonical maps of the
open immersions `U.ι` and `V.ι` — so splitness transfers between `b` restricted to `V` and the
canonical map of `j`.

## What is not done here

[Stacks, Tag 0474] speaks of the full sequence, and this file only touches its second arrow.
The rest of the tag is in
`StacksFrontier.AlgebraicGeometry.ConormalSequenceSplit.ShortExact`, which is where the
three-term sequence `Stacks.ConormalSequenceRight.conormalShortComplex` of [Stacks, Tag 01UZ] —
whose first arrow is `Stacks.ConormalSequenceRight.conormalDifferential` — is shown to be split
short exact under a *global* left inverse, and where the source's final assertion about
`𝒞_{S/X} ⟶ s^*Ω_{X/S}` for a section is proved.

* **Split exactness of the three-term sequence is not stated here**, only splitness of its
  second arrow; see the file above. The first arrow `𝒞_{Z/X} ⟶ i^*Ω_{X/S}` is
  `Stacks.ConormalSequenceRight.conormalDifferential`.
* **The local clause is split between the two files.** What is below is the local splitting of
  the second arrow; short exactness under the same local hypothesis is
  `Stacks.ConormalSequenceSplit.conormalShortComplex_shortExact_of_localRetraction`, and the
  `CategoryTheory.ShortComplex.Splitting` of the sequence *restricted* to such a neighbourhood
  that the two combine into is
  `Stacks.ConormalSequenceSplit.forall_exists_nonempty_splitting_restrict_of_localRetraction`.
  The exactness of restriction along an open immersion that this uses is
  `AlgebraicGeometry.Scheme.Modules.shortExact_map_restrictFunctor`.
* **The affine route is not used.** The source deduces local split exactness from
  [Stacks, Tag 02HP] in the affine case; the splitting of the second arrow here comes from the
  left inverse in every case, so nothing in this file is proved under a hypothesis weaker than
  the existence of a local left inverse. (The *injectivity* half, in the file above, does go
  through [Stacks, Tag 02HP], at the local rings rather than on an affine chart.)

## References

* [Stacks Project, Tag 0474](https://stacks.math.columbia.edu/tag/0474)
* [Stacks Project, Tag 01UZ](https://stacks.math.columbia.edu/tag/01UZ)
* [Stacks Project, Tag 01UV](https://stacks.math.columbia.edu/tag/01UV)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.ConormalSequenceSplit

open AlgebraicGeometry.Scheme.Hom

/-- A split epimorphism preceded by an isomorphism is a split epimorphism. -/
private theorem isSplitEpi_of_isIso_comp {C : Type*} [Category* C] {A B D : C}
    (a : A ⟶ B) {f : B ⟶ D} [IsIso a] (h : IsSplitEpi (a ≫ f)) : IsSplitEpi f := by
  rw [show f = inv a ≫ a ≫ f by simp]
  infer_instance

/-- A split epimorphism followed by an isomorphism is a split epimorphism. -/
private theorem isSplitEpi_of_comp_isIso {C : Type*} [Category* C] {A B D : C}
    {f : A ⟶ B} (b : B ⟶ D) [IsIso b] (h : IsSplitEpi (f ≫ b)) : IsSplitEpi f := by
  rw [show f = (f ≫ b) ≫ inv b by simp]
  infer_instance

/-- Splitness of the image of a morphism under a functor depends on the functor only up to
isomorphism: the section is conjugated by the components of the natural isomorphism. -/
private theorem isSplitEpi_map_of_natIso {C D : Type*} [Category* C] [Category* D] {F G : C ⥤ D}
    (α : F ≅ G) {A B : C} (h : A ⟶ B) (hG : IsSplitEpi (G.map h)) : IsSplitEpi (F.map h) := by
  refine IsSplitEpi.mk' ⟨α.hom.app B ≫ CategoryTheory.section_ (G.map h) ≫ α.inv.app A, ?_⟩
  rw [Category.assoc, Category.assoc, ← α.inv.naturality h,
    ← Category.assoc (CategoryTheory.section_ (G.map h)), IsSplitEpi.id, Category.id_comp,
    Iso.hom_inv_id_app]

variable {Z X S : Scheme.{u}}

/-- **A left inverse over the base splits the canonical map `i^*Ω_{X/S} ⟶ Ω_{Z/S}`.**  If
`g : X ⟶ Z` satisfies `i ≫ g = 𝟙 Z` and is a morphism over `S`, then the canonical map of
[Stacks, Tag 01UV] attached to `i` and the identity of `S` is a split epimorphism.

The right inverse is the source's `i^*c_g`: the canonical map `c` of `g` is pulled back along `i`
and precomposed with the comparison isomorphisms identifying `Ω_{Z/S}` with `i^*g^*Ω_{Z/S}`
through `i ≫ g = 𝟙 Z`.  That this is a right inverse is uniqueness of the canonical map of the
identity of `Z`, the composite being the canonical map of `i ≫ g` by functoriality in the source
morphism.

Nothing is assumed about `i`; in particular it need not be an immersion. -/
theorem isSplitEpi_relativeDifferentialsMap_of_retraction
    (i : Z ⟶ X) (p : X ⟶ S) (q : Z ⟶ S) (hq : i ≫ p = q)
    (g : X ⟶ Z) (hg : i ≫ g = 𝟙 Z) (hgS : g ≫ q = p) :
    IsSplitEpi (relativeDifferentialsMap i p q (𝟙 S)
      (hq.trans (Category.comp_id q).symm)) := by
  have hbm : IsRelativeDifferentialsMap i p q
      (relativeDifferentialsMap i p q (𝟙 S) (hq.trans (Category.comp_id q).symm)) :=
    isRelativeDifferentialsMap_relativeDifferentialsMap i p q (𝟙 S) _
  have hcm : IsRelativeDifferentialsMap g q p
      (relativeDifferentialsMap g q p (𝟙 S) (hgS.trans (Category.comp_id p).symm)) :=
    isRelativeDifferentialsMap_relativeDifferentialsMap g q p (𝟙 S) _
  have e1 := ((hcm.comp hbm).congr_left hg).unique (𝟙 S) (by simp)
    (isRelativeDifferentialsMap_id q)
  refine IsSplitEpi.mk' ⟨(Scheme.Modules.pullbackId Z).inv.app (relativeDifferentials q) ≫
    (Scheme.Modules.pullbackCongr hg).inv.app (relativeDifferentials q) ≫
    (Scheme.Modules.pullbackComp i g).inv.app (relativeDifferentials q) ≫
    (Scheme.Modules.pullback i).map
      (relativeDifferentialsMap g q p (𝟙 S) (hgS.trans (Category.comp_id p).symm)), ?_⟩
  simp only [Category.assoc]
  rw [e1]
  exact (Scheme.Modules.pullbackId Z).inv_hom_id_app (relativeDifferentials q)

/-- **[Stacks, Tag 0474], a left inverse splits the second arrow.**  For an immersion
`i : Z ⟶ X` of schemes over `S` admitting a left inverse `g : X ⟶ Z` over `S`, the second arrow
`i^*Ω_{X/S} ⟶ Ω_{Z/S}` of the conormal sequence of [Stacks, Tag 01UZ] is a split epimorphism.

Together with `Stacks.ConormalSequenceRight.differentialsMapOver_epi` this is the right-hand half
of the source's conclusion. Split exactness of the three-term sequence, which this statement
supplies the section for, is
`Stacks.ConormalSequenceSplit.conormalShortComplexSplitting_of_retraction`. -/
@[stacks 0474 "a left inverse splits the second arrow"]
theorem isSplitEpi_differentialsMapOver_of_retraction (i : Z ⟶ X) [IsImmersion i] (p : X ⟶ S)
    (g : X ⟶ Z) (hg : i ≫ g = 𝟙 Z) (hgS : g ≫ (i ≫ p) = p) :
    IsSplitEpi (relativeDifferentialsMap i p (i ≫ p) (𝟙 S) (by simp)) :=
  isSplitEpi_relativeDifferentialsMap_of_retraction i p (i ≫ p) rfl g hg hgS

/-- **A left inverse of `i` over an open splits the canonical map `i^*Ω_{X/S} ⟶ Ω_{Z/S}` over
that open.**  Let `V` be an open of `Z` and `U` an open of `X` through which `i` restricted to
`V` factors as `j : V ⟶ U`, and let `g : U ⟶ V` be a left inverse of `j` over `S`.  Then the
restriction to `V` of the canonical map of `i` is a split epimorphism.

The canonical map of `V ↪ Z ⟶ X` is computed in two ways by functoriality in the source
morphism: through `U`, where the factors other than the canonical map of `j` are isomorphisms,
and through `Z`, where the factors other than the restriction of the canonical map of `i` are
isomorphisms. -/
theorem isSplitEpi_relativeDifferentialsMap_restrict_of_localRetraction
    (i : Z ⟶ X) (p : X ⟶ S) (V : Z.Opens) (U : X.Opens)
    (j : V.toScheme ⟶ U.toScheme) (hfac : V.ι ≫ i = j ≫ U.ι)
    (g : U.toScheme ⟶ V.toScheme) (hg : j ≫ g = 𝟙 V.toScheme)
    (hgS : g ≫ (V.ι ≫ i ≫ p) = U.ι ≫ p) :
    IsSplitEpi ((Scheme.Modules.pullback V.ι).map
      (relativeDifferentialsMap i p (i ≫ p) (𝟙 S) (by simp))) := by
  have hq : j ≫ (U.ι ≫ p) = V.ι ≫ i ≫ p := by
    rw [← Category.assoc, ← hfac, Category.assoc]
  have hj := isSplitEpi_relativeDifferentialsMap_of_retraction j (U.ι ≫ p)
    (V.ι ≫ i ≫ p) hq g hg hgS
  have hVi : (V.ι ≫ i) ≫ p = (V.ι ≫ i ≫ p) ≫ 𝟙 S := by simp
  have hUm := isRelativeDifferentialsMap_relativeDifferentialsMap U.ι p (U.ι ≫ p) (𝟙 S)
    (by simp)
  have hjm := isRelativeDifferentialsMap_relativeDifferentialsMap j (U.ι ≫ p)
    (V.ι ≫ i ≫ p) (𝟙 S) (hq.trans (Category.comp_id _).symm)
  have eA := ((hUm.comp hjm).congr_left hfac.symm).eq_relativeDifferentialsMap (𝟙 S) hVi
  have hA : IsSplitEpi (relativeDifferentialsMap (V.ι ≫ i) p (V.ι ≫ i ≫ p) (𝟙 S) hVi) := by
    rw [← eA]
    infer_instance
  have hbm := isRelativeDifferentialsMap_relativeDifferentialsMap i p (i ≫ p) (𝟙 S)
    (by simp)
  have hVm := isRelativeDifferentialsMap_relativeDifferentialsMap V.ι (i ≫ p)
    (V.ι ≫ i ≫ p) (𝟙 S) (by simp)
  have eB := (hbm.comp hVm).eq_relativeDifferentialsMap (𝟙 S) hVi
  rw [← eB] at hA
  exact isSplitEpi_of_comp_isIso _ (isSplitEpi_of_isIso_comp _ hA)

/-- **The same, for restriction rather than inverse image.**  The hypotheses are those of
`Stacks.ConormalSequenceSplit.isSplitEpi_relativeDifferentialsMap_restrict_of_localRetraction`
and the conclusion is the same statement for
`AlgebraicGeometry.Scheme.Modules.restrictFunctor V.ι`, the restriction of a sheaf of modules to
the open `V`.

The two functors are naturally isomorphic by
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`; this is the spelling in which the
restricted conormal sequence is known short exact, so it is the one the splitting of that
sequence consumes. -/
theorem isSplitEpi_differentialsMapOver_restrictFunctor_of_localRetraction
    (i : Z ⟶ X) (p : X ⟶ S) (V : Z.Opens) (U : X.Opens)
    (j : V.toScheme ⟶ U.toScheme) (hfac : V.ι ≫ i = j ≫ U.ι)
    (g : U.toScheme ⟶ V.toScheme) (hg : j ≫ g = 𝟙 V.toScheme)
    (hgS : g ≫ (V.ι ≫ i ≫ p) = U.ι ≫ p) :
    IsSplitEpi ((Scheme.Modules.restrictFunctor V.ι).map
      (relativeDifferentialsMap i p (i ≫ p) (𝟙 S) (by simp))) :=
  isSplitEpi_map_of_natIso (Scheme.Modules.restrictFunctorIsoPullback V.ι) _
    (isSplitEpi_relativeDifferentialsMap_restrict_of_localRetraction i p V U j hfac g hg hgS)

/-- **[Stacks, Tag 0474], a local left inverse locally splits the second arrow.**  Let
`i : Z ⟶ X` be an immersion of schemes over `S` which *locally has a left inverse*: every point
`z` of `Z` has an open neighbourhood `V` which `i` maps into an open `U` of `X`, the restricted
morphism `j : V ⟶ U` admitting a left inverse `g : U ⟶ V` over `S`.  Then the second arrow
`i^*Ω_{X/S} ⟶ Ω_{Z/S}` of the conormal sequence of [Stacks, Tag 01UZ] restricts to a split
epimorphism on a neighbourhood of every point of `Z`.

This is the "(locally)" reading of the source's hypothesis and conclusion, on the second arrow.
Local split exactness of the three-term sequence is
`Stacks.ConormalSequenceSplit.forall_exists_nonempty_splitting_restrict_of_localRetraction`,
which combines this splitting with the short exactness
`Stacks.ConormalSequenceSplit.conormalShortComplex_shortExact_of_localRetraction` proved under
the same hypothesis. -/
@[stacks 0474 "a local left inverse locally splits the second arrow"]
theorem forall_exists_isSplitEpi_restrict_of_localRetraction
    (i : Z ⟶ X) [IsImmersion i] (p : X ⟶ S)
    (hloc : ∀ z : Z, ∃ (V : Z.Opens) (U : X.Opens) (j : V.toScheme ⟶ U.toScheme)
      (g : U.toScheme ⟶ V.toScheme), z ∈ V ∧ V.ι ≫ i = j ≫ U.ι ∧ j ≫ g = 𝟙 V.toScheme ∧
        g ≫ (V.ι ≫ i ≫ p) = U.ι ≫ p) :
    ∀ z : Z, ∃ V : Z.Opens, z ∈ V ∧
      IsSplitEpi ((Scheme.Modules.pullback V.ι).map
        (relativeDifferentialsMap i p (i ≫ p) (𝟙 S) (by simp))) := by
  intro z
  obtain ⟨V, U, j, g, hzV, hfac, hg, hgS⟩ := hloc z
  exact ⟨V, hzV, isSplitEpi_relativeDifferentialsMap_restrict_of_localRetraction
    i p V U j hfac g hg hgS⟩

/-- **A section of `p : X ⟶ S` satisfies the hypothesis of [Stacks, Tag 0474].**  A section
`s : S ⟶ X` of `p` is an immersion over `S` ([Stacks, Tag 01KT]) whose left inverse over `S` is
`p` itself, so the second arrow `s^*Ω_{X/S} ⟶ Ω_{S/S}` is a split epimorphism.

The source's assertion for a section is that the *first* arrow `𝒞_{S/X} ⟶ s^*Ω_{X/S}` is an
isomorphism, which is
`Stacks.ConormalSequenceSplit.isIso_conormalDifferential_of_section`; this is the hypothesis
half it rests on. -/
theorem isSplitEpi_relativeDifferentialsMap_of_section (p : X ⟶ S) (s : S ⟶ X)
    (hs : s ≫ p = 𝟙 S) :
    IsSplitEpi (relativeDifferentialsMap s p (s ≫ p) (𝟙 S) (by simp)) :=
  isSplitEpi_relativeDifferentialsMap_of_retraction s p (s ≫ p) rfl p hs
    (by rw [hs, Category.comp_id])

/-- A section of a morphism of schemes is an immersion: [Stacks, Tag 01KT], in the form in which
`Stacks.ConormalSequenceSplit.isSplitEpi_relativeDifferentialsMap_of_section` instantiates
`Stacks.ConormalSequenceSplit.isSplitEpi_differentialsMapOver_of_retraction`. -/
@[ega "IV 16.2.3" "partial"]
theorem isImmersion_of_section (p : X ⟶ S) (s : S ⟶ X) (hs : s ≫ p = 𝟙 S) : IsImmersion s := by
  have : IsImmersion (s ≫ p) := by
    rw [hs]
    infer_instance
  exact IsImmersion.of_comp s p

end Stacks.ConormalSequenceSplit

end
