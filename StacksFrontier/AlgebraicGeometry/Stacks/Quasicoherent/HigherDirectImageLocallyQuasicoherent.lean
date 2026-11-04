module

public import StacksFrontier.AlgebraicGeometry.Stacks.ModuleSheafHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeNaturality
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentSmoothDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAxioms

/-!
# Higher direct images of locally quasi-coherent modules (Stacks 075Z)

Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact and quasi-separated 1-morphism of algebraic stacks over `S`
(**Stacks 050U** and **Stacks 04YW**) and let `ℱ` be a locally quasi-coherent `𝒪_𝒳`-module on
`𝒳_étale` (**Stacks 06WJ**). **Stacks 075Z** says that each higher direct image `Rⁱf_*ℱ`,
computed in the étale topology, is locally quasi-coherent on `𝒴_étale`. The higher direct images
are `AlgebraicGeometry.Stack.moduleSheafHigherDirectImage`, and the assertion itself is
`AlgebraicGeometry.Stack.IsLocallyQuasicoherentHigherDirectImage`.

This file proves hypotheses (2) and (3) of the criterion of **Stacks 076Z** for local
quasi-coherence: local quasi-coherence is preserved by inverse image along a 1-morphism of
algebraic stacks, and it is detected by inverse image along a jointly surjective family of smooth
1-morphisms.

## Main definitions

* `AlgebraicGeometry.Stack.IsLocallyQuasicoherentHigherDirectImage`: the assertion of
  **Stacks 075Z** at a 1-morphism of algebraic stacks and a degree, namely that the higher direct
  image of every locally quasi-coherent module is locally quasi-coherent.

## Main results

* `AlgebraicGeometry.Stack.isLocallyQuasicoherent_of_iso`: local quasi-coherence transports along
  an isomorphism of presheaves of modules.
* `AlgebraicGeometry.Stack.hasSheafify_associatedTopology_of_category_succ` and
  `AlgebraicGeometry.Stack.wEqualsLocallyBijective_associatedTopology_of_category_succ`: the
  sheafification hypotheses under which the higher direct images exist hold at the seating of the
  2-category of algebraic stacks.
* `AlgebraicGeometry.Stack.isLocallyQuasicoherent_stackModulePresheafPullback`: hypothesis (2) of
  **Stacks 076Z** for local quasi-coherence.
* `AlgebraicGeometry.Stack.isLocallyQuasicoherent_iff_forall_isSmooth_jointlySurjective`:
  hypothesis (3) of **Stacks 076Z** for local quasi-coherence.
* `AlgebraicGeometry.Stack.isLocallyQuasicoherent_moduleSheafHigherDirectImage_zero_iff`: in
  degree zero, local quasi-coherence of the higher direct image is that of the direct image.

## References

* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050U](https://stacks.math.columbia.edu/tag/050U)
* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 06WL](https://stacks.math.columbia.edu/tag/06WL)
* [Stacks Project, Tag 06WM](https://stacks.math.columbia.edu/tag/06WM)
* [Stacks Project, Tag 072G](https://stacks.math.columbia.edu/tag/072G)
* [Stacks Project, Tag 0720](https://stacks.math.columbia.edu/tag/0720)
* [Stacks Project, Tag 075H](https://stacks.math.columbia.edu/tag/075H)
* [Stacks Project, Tag 075N](https://stacks.math.columbia.edu/tag/075N)
* [Stacks Project, Tag 075P](https://stacks.math.columbia.edu/tag/075P)
* [Stacks Project, Tag 075Y](https://stacks.math.columbia.edu/tag/075Y)
* [Stacks Project, Tag 075Z](https://stacks.math.columbia.edu/tag/075Z)
* [Stacks Project, Tag 076Z](https://stacks.math.columbia.edu/tag/076Z)
-/


@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w v' w' m t s

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- Local quasi-coherence (**Stacks 06WJ**) transports along an isomorphism of presheaves of
modules over the structure sheaf of a category fibred in groupoids. -/
theorem isLocallyQuasicoherent_of_iso {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    {F G : PresheafOfModules.{m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj} (e : F ≅ G)
    (hF : IsLocallyQuasicoherent B E h S hS p hp F) :
    IsLocallyQuasicoherent B E h S hS p hp G := by
  refine ⟨(Presheaf.isSheaf_of_iso_iff ((PresheafOfModules.toPresheaf
    (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj).mapIso e)).1 hF.1, fun x => ?_⟩
  obtain ⟨hM, hQC⟩ := hF.2 x
  let Rsmall := SmallEtale.structureSheaf E (p.obj x).left.1 (contains_base B E h S hS p x)
  let er := (restrictModuleToSmallEtaleFunctor.{u, v, w, m} B E h S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B) x).mapIso e
  have hMG : Presheaf.IsSheaf
      (SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) G).presheaf :=
    (Presheaf.isSheaf_of_iso_iff ((PresheafOfModules.toPresheaf Rsmall.obj).mapIso er)).1 hM
  exact ⟨hMG, SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((SheafOfModules.fullyFaithfulForget Rsmall).preimageIso er :
      (⟨_, hM⟩ : SheafOfModules.{m} Rsmall) ≅ ⟨_, hMG⟩) hQC⟩

section Sheafification

/-- The associated étale site of a category fibred in groupoids whose objects lie in
`Type (u + 1)` and whose morphisms lie in `Type u` admits sheafification of abelian sheaves at
section universe `u + 1`. -/
theorem hasSheafify_associatedTopology_of_category_succ {𝒳 : Type (u + 1)} [Category.{u} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) :
    HasSheafify (associatedTopology B S hS p (etaleTopology B)) AddCommGrpCat.{u + 1} :=
  have : EssentiallySmall.{u + 1} 𝒳 := inferInstance
  hasSheafifyEssentiallySmallSite _ _

/-- The associated étale site of a category fibred in groupoids whose objects lie in
`Type (u + 1)` and whose morphisms lie in `Type u` has the property that the local isomorphisms
of abelian sheaves at section universe `u + 1` are the locally bijective morphisms. -/
theorem wEqualsLocallyBijective_associatedTopology_of_category_succ {𝒳 : Type (u + 1)}
    [Category.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) :
    (associatedTopology B S hS p (etaleTopology B)).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} :=
  have : EssentiallySmall.{u + 1} 𝒳 := inferInstance
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

end Sheafification

section SmoothLocal

variable {𝒵 𝒳 : AlgebraicStacks.{u, t} B S hS}

/-- **Hypothesis (2) of Stacks 076Z for local quasi-coherence.** The inverse image of a locally
quasi-coherent module along a 1-morphism of algebraic stacks is locally quasi-coherent. -/
theorem isLocallyQuasicoherent_stackModulePresheafPullback (g : 𝒵 ⟶ 𝒳)
    (F : PresheafOfModules.{m} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hF : IsLocallyQuasicoherent B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F) :
    IsLocallyQuasicoherent B E h S hS
      (CatFiberedInGroupoids.homFunctor g.hom ⋙ 𝒳.val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS g.hom)
      ((stackModulePresheafPullback.{u, t, m} B S hS g).obj F) :=
  isLocallyQuasicoherent_modulePullback.{u, u + 1, u, u + 1, u, m} B E h S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (CatFiberedInGroupoids.homFunctor g.hom)
    (isFiberedInGroupoids_homFunctor_comp B S hS g.hom)
    (isFibredOneMorphism_homFunctor_comp B S hS g.hom) F hF

/-- **Hypothesis (3) of Stacks 076Z for local quasi-coherence**, and with it hypothesis (2). Let
`f j : 𝒵 j ⟶ 𝒳` be a family of smooth 1-morphisms of algebraic stacks over `S` whose images
cover the points of `𝒳`, that is `|𝒳| = ⋃ j, |f j|(|𝒵 j|)`, and let `F` be a sheaf of
`𝒪_𝒳`-modules on `𝒳_étale`. Then `F` is locally quasi-coherent if and only if every inverse
image `f j^{-1} F` is. -/
theorem isLocallyQuasicoherent_iff_forall_isSmooth_jointlySurjective {J : Type s}
    {𝒲 : J → AlgebraicStacks.{u, t} B S hS} (f : ∀ j, 𝒲 j ⟶ 𝒳)
    (hsmooth : ∀ j, AlgebraicStacks.IsSmooth B S hS (f j))
    (hjs : (Set.univ : Set (AlgebraicStacks.points B S hS 𝒳)) =
      ⋃ j, Set.range (AlgebraicStacks.pointsMap B S hS (f j)))
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hF : Presheaf.IsSheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      F.presheaf) :
    IsLocallyQuasicoherent B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F ↔
      ∀ j, IsLocallyQuasicoherent B E h S hS
        (CatFiberedInGroupoids.homFunctor (f j).hom ⋙ 𝒳.val.val.p)
        (isFiberedInGroupoids_homFunctor_comp B S hS (f j).hom)
        ((stackModulePresheafPullback.{u, t, u} B S hS (f j)).obj F) :=
  ⟨fun hlqc j =>
      isLocallyQuasicoherent_stackModulePresheafPullback.{u, u, t} B E h S hS (f j) F hlqc,
    fun hlqc =>
      isLocallyQuasicoherent_of_isSmooth_jointlySurjective B E h S hS f hsmooth hjs F hF hlqc⟩

end SmoothLocal

section DegreeZero

variable {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (g : 𝒳 ⥤ 𝒴) (hg : g ⋙ q = p)
  [HasWeakSheafify (associatedTopology B S hS p (etaleTopology B))
    AddCommGrpCat.{max u v w v' w'}]
  [(associatedTopology B S hS p (etaleTopology B)).WEqualsLocallyBijective
    AddCommGrpCat.{max u v w v' w'}]
  [HasWeakSheafify (associatedTopology B S hS q (etaleTopology B))
    AddCommGrpCat.{max u v w v' w'}]
  [(associatedTopology B S hS q (etaleTopology B)).WEqualsLocallyBijective
    AddCommGrpCat.{max u v w v' w'}]

/-- In degree zero the higher direct image of a sheaf of modules is the direct image of
**Stacks 06WE**, so it is locally quasi-coherent exactly when the direct image is. -/
theorem isLocallyQuasicoherent_moduleSheafHigherDirectImage_zero_iff
    (M : SheafOfModules.{max u v w v' w'} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))) :
    IsLocallyQuasicoherent B E h S hS q hq
        (((moduleSheafHigherDirectImage B S hS p q hp hq g hg (etaleTopology B)
          (etaleTopology_le_topology B) 0).obj M).val) ↔
      IsLocallyQuasicoherent B E h S hS q hq
        (((moduleSheafPushforward.{u, v, w, u, v', w'} B S hS p q hp hq g hg (etaleTopology B)
          (etaleTopology_le_topology B)).obj M).val) := by
  have e := (SheafOfModules.forget (ringStructureSheafCore B S hS q hq (etaleTopology B)
    (etaleTopology_le_topology B))).mapIso ((moduleSheafHigherDirectImageZeroIso B S hS p q hp hq
      g hg (etaleTopology B) (etaleTopology_le_topology B)).app M)
  exact ⟨isLocallyQuasicoherent_of_iso B E h S hS q hq e,
    isLocallyQuasicoherent_of_iso B E h S hS q hq e.symm⟩

end DegreeZero

/-- **The assertion of Stacks 075Z** at a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S`
and a degree `i`: the higher direct image `Rⁱf_*ℱ`, computed in the étale topology, of every
locally quasi-coherent `𝒪_𝒳`-module `ℱ` on `𝒳_étale` is locally quasi-coherent on `𝒴_étale`.

**Stacks 075Z** says this holds whenever `f` is quasi-compact and quasi-separated. The source of
`f` is presented strictly, its structure functor being the morphism's functor followed by the
structure functor of the target. -/
noncomputable abbrev IsLocallyQuasicoherentHigherDirectImage
    {𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS} (f : 𝒳 ⟶ 𝒴) (i : ℕ) : Prop :=
  let := hasSheafify_associatedTopology_of_category_succ B S hS
    (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
  let := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS
    (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
  let := hasSheafify_associatedTopology_of_category_succ B S hS 𝒴.val.val.p
  let := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS 𝒴.val.val.p
  ∀ F : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS f.hom)
      (etaleTopology B) (etaleTopology_le_topology B)),
    IsLocallyQuasicoherent B E h S hS
        (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
        (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) F.val →
      IsLocallyQuasicoherent B E h S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
        ((moduleSheafHigherDirectImage.{u, u + 1, u, u + 1, u} B S hS
          (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p) 𝒴.val.val.p
          (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) 𝒴.val.isFiberedInGroupoids
          (CatFiberedInGroupoids.homFunctor f.hom) rfl (etaleTopology B)
          (etaleTopology_le_topology B) i).obj F).val

end AlgebraicGeometry.Stack

end
