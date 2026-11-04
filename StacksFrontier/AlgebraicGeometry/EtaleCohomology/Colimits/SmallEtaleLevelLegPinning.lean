module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleLevelObjectSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleOpensLeg
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleColimitPresentationAdjointForm
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleCohomologyDegreeZeroSections

/-!
# The leg of a level, read on sections over an object, is the transpose of the geometric leg

`Stacks.WeakSites.ColimitGlobalSections.sectionOver_colimit_of_oneHypercoverOf_ab` — the
degree-zero step of [Stacks, Tag 09YQ] over an object that neither the levels of
[Stacks, Tag 0EYL] nor their colimit site contain — quantifies over a map `ρ` from the sections of
`F_n` over an object of an ambient site of the level to the sections of `𝓕` over an object of an
ambient site of the limit, and **pins** it by one condition `hρ`: restricted to the image of the
object `W₀ k` of the one-hypercover datum, `ρ t` is the leg of the level applied to the
restriction of `t`.

The leg of the level is `Stacks.EtaleCohomology.AffineLimitCohomology.levelPullbackLeg`, built out
of the *transposed* family `Stacks.EtaleCohomology.systemDirLeg` of a family of maps out of the
inverse images; the geometric maps a consumer has are
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.PresentedSystem.legSection` (for the degree-zero
statement `H0`) and `Stacks.EtaleCohomology.opensSectionsLeg` (for the surjectivity `hqc` of
`Stacks.EtaleCohomology.sectionsDifference_of_isCompact_surjective_opensLeg`), both built out of
`Stacks.EtaleCohomology.etaleTransposeSection`, the transpose read on sections over an object.
Nothing in the tree related the two: the module docstring of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/SmallEtaleLevelObjectSections.lean` records
that comparison as the whole of what those two statements still owe.

**This file is that comparison.** It is one level at a time and there is no colimit anywhere in
it.

## Main results

* `Stacks.EtaleCohomology.systemDirLeg_transportLeg_hom_app` — **the two transposes agree.** The
  transposed leg `systemDirLeg` of the family a presentation carries, read on sections over an
  object `Z` of Mathlib's small étale site of a level, *is*
  `Stacks.EtaleCohomology.etaleTransposeSection` of the leg in the vocabulary of the constructed
  inverse image.
* `Stacks.EtaleCohomology.AffineLimitCohomology.levelPullbackLeg_app_eq` — consequently the leg of
  the level presentation over an object of a level is that transpose, followed by the transport
  along the level crossing.
* `Stacks.EtaleCohomology.AffineLimitCohomology.levelPullbackLeg_comp_app` and
  `levelPullbackLeg_app_apply` — **THE PINNING LEMMA**, in morphism and in element form: for a
  morphism `g` of Mathlib's small étale site of the level out of the image of an object of the
  level, restricting a section along `g` and then applying the level leg is applying the transpose
  over the target of `g` and then restricting along the base change of `g` and the level crossing.
* `Stacks.EtaleCohomology.opensSectionsLeg_eq_etaleTransposeSection` and
  `Stacks.EtaleCohomology.etaleSectionsRestriction_comp_eq` — the two geometric maps, read as that
  same transpose followed by one restriction. The first is the definition of
  `Stacks.EtaleCohomology.opensSectionsLeg` named; the second is the content for the leg on global
  sections, where the restriction is along the unique map from the terminal object.

## How the comparison goes, and why it is not a formality

**The two inverse images.** `Stacks.EtaleCohomology.etaleTransposeSection` transposes across
`Stacks.EtaleCohomology.etaleAbelianInverseImageDirectImageAdj`, whose left adjoint is the inverse
image built as a left Kan extension followed by sheafification; `systemDirLeg` transposes across
`Stacks.EtaleCohomology.smallEtaleAdjunctionAb`, whose left adjoint is the abstract left adjoint
of the direct image. The two adjunctions have the **same right adjoint** — direct image is
restriction along base change, with no left adjoint and no sheafification in it — so a leg for one
becomes a leg for the other along
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.inverseImageIsoPullbackAb`, which is
`CategoryTheory.Adjunction.leftAdjointUniq`, and the two transposes then agree by
`CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_hom_app_comp`. No new coherence is proved
here; that lemma is proved in
`StacksFrontier/CategoryTheory/Adjunction/Mates.lean` and this is its consumer at the étale sites.

**The restriction.** Everything else is the naturality
`Stacks.EtaleCohomology.etaleTransposeSection_naturality` of the transpose in the object of the
site, which is where the restriction along the leg `fVn a k` of the one-hypercover datum is
absorbed. The associativity is done in an arbitrary category and applied by `exact`
(`comp_eq_of_eq_of_naturality`), for the reason the implementation notes of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/SmallEtaleLevelCocyclePresentation.lean`
record: a goal mentioning an object of `AlgebraicGeometry.Scheme.Etale` is not type-correct at the
transparency `rewrite` builds its motive at.

## What this leaves, and one statement it shows cannot be proved

What the two consumers still owe, after this file, is **geometric and not about sections**: the
commuting square comparing the leg `fV k` of the datum at the limit with the base change of the
leg `fVn a k` at the level, through
`Stacks.EtaleCohomology.AffineLimitCohomology.levelCrossingIso`; and, for either consumer, the
identification of the base changes `Stacks.EtaleCohomology.QcSeparatedColimit`
`.toLimitBaseChangeEtaleObj` and `.transitionBaseChangeEtaleObj` of the datum's object `V₀` with
the geometric object the consumer speaks about — an open subscheme's preimage for
`opensSectionsLeg`, the terminal object for the leg on global sections. Both objects have a
**monomorphic structure morphism** (an open immersion, respectively an identity), so
`Stacks.EtaleCohomology.etale_hom_ext_of_mono` closes the square with no fibre product computed;
that is the shape the remaining work has.

**The surjectivity `hqc` is stated pointwise, because the uniform form is false.**
`Stacks.EtaleCohomology.surjective_opensSectionsLeg_of_isCompact` and the hypothesis `hsurj` of
`Stacks.EtaleCohomology.OpensAcyclicity.sectionsDifference_of_surjective_opensLeg` do not ask,
for an open `W` of a level, for a level `j` at which `opensSectionsLeg` is **surjective** — the
level chosen before the section. What a filtered colimit of groups gives, and what
`sectionOver_colimit_of_oneHypercoverOf_ab` concludes, is the *pointwise* statement: each section
comes from some level, the level depending on the section. The two are not interchangeable, and
the stronger one is false: for a constant system of schemes over `ℕ` with `F_i` the constant sheaf
on `⊕_{p < i} ℤ` and the transitions the inclusions, `𝓕 = colim_i f_i^{-1}F_i` is the constant
sheaf on `⊕_{p < ω} ℤ`, and no `F_j(X_j) ⟶ 𝓕(X)` is surjective while every section of `𝓕` does
come from some level. Both statements carry the pointwise hypothesis, which costs their
consumers nothing — surjectivity is only ever needed on the section the consumer is handed, which
is what
`Stacks.EtaleCohomology.OpensAcyclicity.exists_sectionsDifference_preimage_of_leg` makes explicit.

## References

* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 0EYL](https://stacks.math.columbia.edu/tag/0EYL)
* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.Sites.InverseSystem
open Stacks.EtaleCohomology.SmallEtaleLimitCohomology (conePi transportLeg)
open Stacks.EtaleCohomology.QcSeparatedColimit (levelIndex)

universe v u

namespace Stacks.EtaleCohomology

/-- **Substituting a factorisation and then a naturality square inside a composite.** The shape in
which the pinning lemma below is assembled: `hT` factors the leg of the level as a transpose
followed by a transport, and `hnat` is the naturality of that transpose in the object of the site.

Stated in an arbitrary category and applied by `exact`, for the reason recorded on
`Stacks.EtaleCohomology.comp_eq_of_conjugate`: a goal mentioning an object of
`AlgebraicGeometry.Scheme.Etale` is not type-correct at the transparency `rewrite` builds its
motive at. -/
theorem comp_eq_of_eq_of_naturality {𝒜 : Type*} [Category* 𝒜] {A₀ A₁ A₂ A₃ A₄ : 𝒜}
    {m : A₀ ⟶ A₁} {T : A₁ ⟶ A₄} {t : A₁ ⟶ A₂} {r : A₂ ⟶ A₄} {t' : A₀ ⟶ A₃} {b : A₃ ⟶ A₂}
    (hT : T = t ≫ r) (hnat : m ≫ t = t' ≫ b) : m ≫ T = t' ≫ b ≫ r := by
  rw [hT, ← Category.assoc, hnat, Category.assoc]

/-! ### The two transposes of a leg -/

section Bridge

variable {I : Type v} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}} (c : Cone D)

/-- **The transposed leg of a system and the transpose of a leg over an object are the same map.**
Let `F` be a system of abelian sheaves on Mathlib's small étale sites of the levels, let `𝓕` be an
abelian sheaf on that of the vertex of a cone, and let `ι_i : f_i^{-1}F_i ⟶ 𝓕` be a family of maps
out of the **constructed** inverse images — the vocabulary
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.IsColimitPresentation` and [Stacks, Tag 09YQ]
state their hypothesis in. Then the transpose
`Stacks.EtaleCohomology.systemDirLeg` of the family read in the abstract inverse-image vocabulary,
evaluated on sections over an object `Z` of the level, is
`Stacks.EtaleCohomology.etaleTransposeSection` of `ι_i` at `Z`.

The two adjunctions have the same right adjoint, so this is
`CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_hom_app_comp` at
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.inverseImageIsoPullbackAb`, which is
`CategoryTheory.Adjunction.leftAdjointUniq` of the two. Nothing is assumed. -/
theorem systemDirLeg_transportLeg_hom_app
    (F : EtaleSheafSystem D AddCommGrpCat.{u + 1})
    (𝓕 : Sheaf (Scheme.smallEtaleTopology c.pt) AddCommGrpCat.{u + 1})
    (ι : ∀ i : Iᵒᵖ, (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) ⟶ 𝓕)
    (i : Iᵒᵖ) (Z : (D.obj i).Etale) :
    (systemDirLeg c F 𝓕 (transportLeg F 𝓕 ι) i).hom.app (op Z) =
      etaleTransposeSection.{u + 1, u} (conePi c i) (ι i) Z :=
  congrArg (fun z : F.obj i ⟶ (smallEtalePushforwardAb (conePi c i)).obj 𝓕 => z.hom.app (op Z))
    (Adjunction.homEquiv_leftAdjointUniq_hom_app_comp
      (smallEtaleAdjunctionAb (conePi c i))
      (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} (conePi c i)) (ι i))

end Bridge

/-! ### The two geometric maps, read as that transpose -/

section Geometric

variable {T S : Scheme.{u}} (k : T ⟶ S)
  {G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}}
  {𝒢 : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}

/-- **The transpose over an object is the unit followed by the leg**, on sections: the component of
`A ⟶ k_*k^{-1}A` over the object, followed by `ι` read over the base change of the object. This is
`CategoryTheory.Adjunction.homEquiv_unit` with the direct image unfolded to restriction along base
change, which is the junction the implementation notes of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/SmallEtaleOpensLeg.lean` record as only
definitional. -/
theorem etaleTransposeSection_eq (ι : (etaleAbelianInverseImage.{u, u + 1} k).obj G ⟶ 𝒢)
    (Z : S.Etale) :
    etaleTransposeSection.{u + 1, u} k ι Z =
      ((etaleAbelianInverseImageDirectImageAdj.{u, u + 1} k).unit.app G).hom.app (op Z) ≫
        ι.hom.app (op ((smallEtaleBaseChange k).obj Z)) := by
  rw [etaleTransposeSection, Adjunction.homEquiv_unit]
  rfl

/-- **The leg on sections over an open subscheme is the transpose over the object that open is,
followed by the identification of its preimage with a base change.** This is the definition of
`Stacks.EtaleCohomology.opensSectionsLeg` named, so that the pinning condition of
[Stacks, Tag 09YQ] may be compared with it without unfolding two definitions at the point of
use. -/
theorem opensSectionsLeg_eq_etaleTransposeSection
    (ι : (etaleAbelianInverseImage.{u, u + 1} k).obj G ⟶ 𝒢) (W : S.Opens) :
    opensSectionsLeg k ι W =
      etaleTransposeSection.{u + 1, u} k ι ((opensToEtale S).obj W) ≫
        𝒢.obj.map (opensToEtaleBaseChangeIso k W).hom.op :=
  rfl

/-- **The leg on global sections is the transpose over the terminal object, followed by restriction
along the unique map from the terminal object of the site upstairs.**

`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.PresentedSystem.legSection` is
`Stacks.EtaleCohomology.etaleSectionsRestriction` followed by the leg over the terminal object
`𝟙 T`; `etaleSectionsRestriction` is the unit over the terminal object `𝟙 S` followed by that same
restriction, so the two differ by the naturality of `ι` in the object of the site and by nothing
else. -/
theorem etaleSectionsRestriction_comp_eq
    (ι : (etaleAbelianInverseImage.{u, u + 1} k).obj G ⟶ 𝒢) :
    etaleSectionsRestriction.{u, u + 1} k G ≫ ι.hom.app (op (Scheme.Etale.mk (𝟙 T))) =
      etaleTransposeSection.{u + 1, u} k ι (Scheme.Etale.mk (𝟙 S)) ≫
        𝒢.obj.map
          ((isTerminalSmallEtaleBaseChangeEtaleMkId.{u} k).from
            (Scheme.Etale.mk (𝟙 T))).op :=
  (Category.assoc _ _ _).trans <|
    (congrArg (etaleUnitSection.{u, u + 1} k G ≫ ·)
      (ι.hom.naturality ((isTerminalSmallEtaleBaseChangeEtaleMkId.{u} k).from
        (Scheme.Etale.mk (𝟙 T))).op)).trans <|
      (Category.assoc _ _ _).symm.trans <|
        congrArg (· ≫ 𝒢.obj.map ((isTerminalSmallEtaleBaseChangeEtaleMkId.{u} k).from
          (Scheme.Etale.mk (𝟙 T))).op) (etaleTransposeSection_eq k ι (Scheme.Etale.mk (𝟙 S))).symm

end Geometric

namespace AffineLimitCohomology

/-! ### The pinning lemma -/

section Level

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ Scheme.{max u v}) (c : Cone D) (B : BigEtaleSite.{max u v})
  (hD : ∀ i, B.Contains (D.obj i)) (hX : B.Contains c.pt) (hc : IsLimit c)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
  (F : EtaleSheafSystem D AddCommGrpCat.{max u v + 1})
  (𝓕 : Sheaf (Scheme.smallEtaleTopology c.pt) AddCommGrpCat.{max u v + 1})
  (ι : ∀ i : Iᵒᵖ,
    (etaleAbelianInverseImage.{max u v, max u v + 1} (conePi c i)).obj (F.obj i) ⟶ 𝓕)

/-- **The leg of the level presentation over an object of a level is the transpose of the
geometric leg, followed by the transport along the level crossing.**
`Stacks.EtaleCohomology.AffineLimitCohomology.levelCocycleLeg_app` with its transposed family
identified by `Stacks.EtaleCohomology.systemDirLeg_transportLeg_hom_app`. -/
theorem levelPullbackLeg_app_eq (n : (sys D c B hD hX hc).I)
    (Y : (sys D c B hD hX hc).C n) :
    (levelPullbackLeg D c B hD hX hc F 𝓕 (transportLeg F 𝓕 ι) n).app (op Y) =
      etaleTransposeSection.{max u v + 1, max u v}
          (conePi c (levelIndex D c B hD hX hc n)) (ι (levelIndex D c B hD hX hc n))
          ((levelEtaleSite D c B hD hX hc n).obj Y) ≫
        𝓕.obj.map ((levelCrossingIso D c B hD hX hc n).hom.app Y).op :=
  congrArg (fun z => z ≫ 𝓕.obj.map ((levelCrossingIso D c B hD hX hc n).hom.app Y).op)
    (systemDirLeg_transportLeg_hom_app c F 𝓕 ι (levelIndex D c B hD hX hc n)
      ((levelEtaleSite D c B hD hX hc n).obj Y))

/-- **THE PINNING LEMMA.** Let `(X_i)` be an inverse system of schemes over a nonempty directed
index with affine transition morphisms, all objects of a big étale site `B`, let `X` be the vertex
of a limit cone, let `F` be a system of abelian sheaves on Mathlib's small étale sites of the `X_i`
in the sense of [Stacks, Tag 0EZL] and let `ι_i : f_i^{-1}F_i ⟶ 𝓕` be a family of maps out of the
inverse images. Let `Y` be an object of a level `n` of [Stacks, Tag 0EYL], let `Z` be an object of
Mathlib's small étale site of the stage `X_n` and let `g` be a morphism from the image of `Y` to
`Z` there. Then restricting a section of `F_n` over `Z` along `g` and applying the leg
`Stacks.EtaleCohomology.AffineLimitCohomology.levelPullbackLeg` of the level presentation over `Y`
is the same as applying the transpose
`Stacks.EtaleCohomology.etaleTransposeSection` of `ι_n` over `Z` and then restricting along the
base change of `g` and the level crossing.

This is the comparison the pinning hypothesis `hρ` of
`Stacks.WeakSites.ColimitGlobalSections.sectionOver_colimit_of_oneHypercoverOf_ab` asks for, with
`g` the leg `fVn a k` of the one-hypercover datum read in Mathlib's site: one level at a time, and
with no colimit in it. The two ingredients are `levelPullbackLeg_app_eq` and the naturality
`Stacks.EtaleCohomology.etaleTransposeSection_naturality` of the transpose in the object; nothing
is assumed, and no identity law on the system is used or available. -/
theorem levelPullbackLeg_comp_app (n : (sys D c B hD hX hc).I)
    (Y : (sys D c B hD hX hc).C n)
    {Z : (D.obj (levelIndex D c B hD hX hc n)).Etale}
    (g : (levelEtaleSite D c B hD hX hc n).obj Y ⟶ Z) :
    (F.obj (levelIndex D c B hD hX hc n)).obj.map g.op ≫
        (levelPullbackLeg D c B hD hX hc F 𝓕 (transportLeg F 𝓕 ι) n).app (op Y) =
      etaleTransposeSection.{max u v + 1, max u v}
          (conePi c (levelIndex D c B hD hX hc n)) (ι (levelIndex D c B hD hX hc n)) Z ≫
        𝓕.obj.map ((smallEtaleBaseChange
            (conePi c (levelIndex D c B hD hX hc n))).map g).op ≫
          𝓕.obj.map ((levelCrossingIso D c B hD hX hc n).hom.app Y).op :=
  Stacks.EtaleCohomology.comp_eq_of_eq_of_naturality
    (levelPullbackLeg_app_eq D c B hD hX hc F 𝓕 ι n Y)
    (etaleTransposeSection_naturality (conePi c (levelIndex D c B hD hX hc n))
      (ι (levelIndex D c B hD hX hc n)) g)

/-- `Stacks.EtaleCohomology.AffineLimitCohomology.levelPullbackLeg_comp_app` read on a section,
which is the form the pinning hypothesis `hρ` of
`Stacks.WeakSites.ColimitGlobalSections.sectionOver_colimit_of_oneHypercoverOf_ab` is stated
in. -/
theorem levelPullbackLeg_app_apply (n : (sys D c B hD hX hc).I)
    (Y : (sys D c B hD hX hc).C n)
    {Z : (D.obj (levelIndex D c B hD hX hc n)).Etale}
    (g : (levelEtaleSite D c B hD hX hc n).obj Y ⟶ Z)
    (t : ToType ((F.obj (levelIndex D c B hD hX hc n)).obj.obj (op Z))) :
    (levelPullbackLeg D c B hD hX hc F 𝓕 (transportLeg F 𝓕 ι) n).app (op Y)
        ((F.obj (levelIndex D c B hD hX hc n)).obj.map g.op t) =
      𝓕.obj.map ((levelCrossingIso D c B hD hX hc n).hom.app Y).op
        (𝓕.obj.map ((smallEtaleBaseChange
            (conePi c (levelIndex D c B hD hX hc n))).map g).op
          (etaleTransposeSection.{max u v + 1, max u v}
            (conePi c (levelIndex D c B hD hX hc n))
            (ι (levelIndex D c B hD hX hc n)) Z t)) :=
  Eq.trans
    (ConcreteCategory.comp_apply
      ((F.obj (levelIndex D c B hD hX hc n)).obj.map g.op)
      ((levelPullbackLeg D c B hD hX hc F 𝓕 (transportLeg F 𝓕 ι) n).app (op Y)) t).symm
    (Eq.trans
      (ConcreteCategory.congr_hom
        (levelPullbackLeg_comp_app D c B hD hX hc F 𝓕 ι n Y g) t)
      (Eq.trans (ConcreteCategory.comp_apply _ _ t)
        (ConcreteCategory.comp_apply _ _ _)))

end Level

end AffineLimitCohomology

end Stacks.EtaleCohomology

end
