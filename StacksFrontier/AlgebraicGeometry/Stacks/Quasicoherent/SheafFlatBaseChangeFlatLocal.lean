module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.CartesianTransport
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatCartesianFppfDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatCartesianRestrictModulePullbackComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentFlatArrowCartesian
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeSmoothCoveringLocal
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.CoveringSieves
public import StacksFrontier.AlgebraicGeometry.Stacks.ObjectStackMapJointlySurjective

/-!
# The flat base change property is local for flat, finitely presented coverings (Stacks 07AQ (2))

Let `f j : 𝒵 j ⟶ 𝒳` be a family of flat and locally finitely presented 1-morphisms of algebraic
stacks with `|𝒳| = ⋃ j, |f j|(|𝒵 j|)`, and let `F` be a sheaf of `𝒪_𝒳`-modules on `𝒳_fppf`.
**Stacks 07AQ** part (2) says: if every `f j^{-1} F` lies in `LQCoh^fbc(𝒪_{𝒵 j})`, then `F` lies in
`LQCoh^fbc(𝒪_𝒳)`. The flat base change property is the one of **Stacks 0762**, for the pullback
of sheaves; nothing is assumed of `F` beyond the fppf sheaf condition. Part (1) is
`isLocallyQuasicoherentWithSheafFlatBaseChange_of_isSmooth_jointlySurjective`.

## Implementation notes

The source runs the argument through the exact sequence `0 → F → a_*a^*F → b_*b^*F` of
Stacks 06XE and Stacks 0771 for direct images. Here it is run through the cartesian property of
modules on affine objects, which characterizes `LQCoh^fbc`, so that neither direct images nor
descent data occur.

* A module in `LQCoh^fbc` is cartesian over the arrows between affine objects lying over flat
  morphisms (`bijective_restrictionBaseChange_of_isLocallyQuasicoherentWithSheafFlatBaseChange`).
  Applied to `f j^{-1} F`, this makes `F` cartesian over the flat arrows between affine objects
  whose target maps to an image of `f j`: such an arrow is isomorphic to the image of an arrow of
  `𝒵 j` (`exists_iso_homFunctor_obj_comp_map`).
* Those targets cover `𝒳` for the fppf topology, by the fppf-local factorization of
  **Stacks 07AN**, and the cartesian property descends along such coverings because `F` is an
  fppf sheaf (`bijective_restrictionBaseChange_of_flat_of_goodCover`).
* A module cartesian over all the flat arrows between affine objects is in `LQCoh^fbc`
  (`isLocallyQuasicoherentWithSheafFlatBaseChange_of_bijective_restrictionBaseChange_of_flat`).

## Main results

* `locallyQuasicoherentSheafFlatBaseChangeFppfModules_of_fppfLocal_image`: `F` lies in
  `LQCoh^fbc(𝒪_𝒳)` as soon as every `f j^{-1} F` does and every object of `𝒳` is covered, for the
  fppf topology, by objects mapping to images of the `f j`.
* `locallyQuasicoherentSheafFlatBaseChangeFppfModules_of_isFlat_isLfp_jointlySurjective`:
  **Stacks 07AQ**, part (2).
* `locallyQuasicoherentSheafFlatBaseChangeFppfModules_of_flatLfp_cover_of_atlas`: the case of the
  family of the 1-morphisms `y j : (Sch/U_j) → 𝒳` of objects `y j ⟶ x₀` lying over a jointly
  surjective family of flat, locally finitely presented morphisms, `x₀` a smooth surjective atlas
  object.

## References

* [Stacks Project, Tag 07AQ](https://stacks.math.columbia.edu/tag/07AQ)
* [Stacks Project, Tag 07AN](https://stacks.math.columbia.edu/tag/07AN)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- **An object mapping to an image of a 1-morphism is isomorphic to an image, compatibly.** For
`g : 𝒵 ⟶ 𝒳` and an arrow `ψ : x ⟶ g(z)` of `𝒳`, pulling `z` back inside `𝒵` along the morphism of
schemes below `ψ` gives `γ : w₀ ⟶ z` with `ψ = ι ≫ g(γ)` for an isomorphism `ι : x ≅ g(w₀)`: the
arrow `ι` lies over an identity, and `𝒳` is fibred in groupoids. -/
theorem exists_iso_homFunctor_obj_comp_map {𝒵 𝒳 : AlgebraicStacks.{u, w} B S hS} (g : 𝒵 ⟶ 𝒳)
    {x : 𝒳.val.val.obj} {z : 𝒵.val.val.obj}
    (ψ : x ⟶ (CatFiberedInGroupoids.homFunctor g.hom).obj z) :
    ∃ (w₀ : 𝒵.val.val.obj) (γ : w₀ ⟶ z)
      (ι : x ≅ (CatFiberedInGroupoids.homFunctor g.hom).obj w₀),
      ι.hom ≫ (CatFiberedInGroupoids.homFunctor g.hom).map γ = ψ := by
  set p := 𝒳.val.val.p with hpdef
  have hfib := 𝒳.val.isFiberedInGroupoids
  have : p.IsFibered := hfib.isFibered
  let G := CatFiberedInGroupoids.homFunctor g.hom
  let q := G ⋙ p
  have : q.IsFibered := (isFiberedInGroupoids_homFunctor_comp B S hS g.hom).isFibered
  let k := p.map ψ
  let w' : 𝒵.val.val.obj := Functor.IsPreFibered.pullbackObj (p := q) (a := z) rfl k
  let γ : w' ⟶ z := Functor.IsPreFibered.pullbackMap (p := q) (a := z) rfl k
  have hγq : q.IsHomLift k γ := inferInstance
  have hγlift : p.IsHomLift k (G.map γ) :=
    IsHomLift.of_fac' (p := p) _ _ (IsHomLift.domain_eq q k γ)
      (IsHomLift.codomain_eq q k γ) (IsHomLift.fac' q k γ)
  have : p.IsStronglyCartesian k (G.map γ) := hfib.isStronglyCartesian_homLift _ _
  have : p.IsHomLift k ψ := IsHomLift.map (p := p) ψ
  let ι : x ⟶ G.obj w' := Functor.IsStronglyCartesian.map p k (G.map γ)
    (Category.id_comp k).symm ψ
  have hιγ : ι ≫ G.map γ = ψ := Functor.IsStronglyCartesian.fac p k _ (Category.id_comp k).symm ψ
  have hιlift : p.IsHomLift (𝟙 (p.obj x)) ι :=
    Functor.IsStronglyCartesian.map_isHomLift p k _ (Category.id_comp k).symm ψ
  have : p.IsStronglyCartesian (𝟙 (p.obj x)) ι := hfib.isStronglyCartesian_homLift _ _
  have : IsIso ι := Functor.IsStronglyCartesian.isIso_of_base_isIso p (𝟙 (p.obj x)) ι
  exact ⟨w', γ, asIso ι, hιγ⟩

/-- **`LQCoh^fbc` is fppf-local through the images of a family of 1-morphisms.** Let
`f j : 𝒵 j ⟶ 𝒳` be 1-morphisms of algebraic stacks and `F` a sheaf of `𝒪_𝒳`-modules on `𝒳_fppf`
every inverse image `f j^{-1} F` of which lies in `LQCoh^fbc(𝒪_{𝒵 j})`. If every object of `𝒳`
has a covering sieve for the fppf topology all of whose members have a source mapping to an image
of some `f j`, then `F` lies in `LQCoh^fbc(𝒪_𝒳)`. -/
theorem locallyQuasicoherentSheafFlatBaseChangeFppfModules_of_fppfLocal_image
    {J : Type v} {𝒵 : J → AlgebraicStacks.{u, w} B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : ∀ j, 𝒵 j ⟶ 𝒳) (F : fppfModules B S hS 𝒳)
    (hlqc : ∀ j, IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, _, _, u} B E h S hS
      (CatFiberedInGroupoids.homFunctor (f j).hom ⋙ 𝒳.val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS (f j).hom)
      ((stackModulePresheafPullback.{u, w, u} B S hS (f j)).obj F.val))
    (hcov : ∀ x : 𝒳.val.val.obj, ∃ R : Sieve x,
      R ∈ BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf x ∧
        ∀ ⦃z : 𝒳.val.val.obj⦄ (g : z ⟶ x), R g → ∃ (j : J) (w₀ : (𝒵 j).val.val.obj),
          Nonempty (z ⟶ (CatFiberedInGroupoids.homFunctor (f j).hom).obj w₀)) :
    lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳 F := by
  classical
  set p := 𝒳.val.val.p with hpdef
  have hp := 𝒳.val.isFiberedInGroupoids
  have : p.IsFibered := hp.isFibered
  have hFfppf : Presheaf.IsSheaf (BigFppfOver.associatedTopology B S hS p .fppf)
      F.val.presheaf := F.isSheaf
  have hFet : Presheaf.IsSheaf (associatedTopology B S hS p (etaleTopology B)) F.val.presheaf :=
    F.isSheaf.of_le (BigFppfOver.associatedTopology_le_fppf B S hS _ .etale)
  let good : 𝒳.val.val.obj → Prop := fun x => ∃ (j : J) (z : (𝒵 j).val.val.obj),
    Nonempty (x ⟶ (CatFiberedInGroupoids.homFunctor (f j).hom).obj z)
  have hgood : ∀ ⦃z y : 𝒳.val.val.obj⦄ (_ : z ⟶ y), good y → good z :=
    fun _ _ a ⟨j, w₀, ⟨b⟩⟩ => ⟨j, w₀, ⟨a ≫ b⟩⟩
  have hcart : ∀ ⦃x₁ x₂ : 𝒳.val.val.obj⦄ (e : x₁ ⟶ x₂), good x₂ →
      IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x₁)) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x₂)) →
      Flat (B.inclusion.map (p.map e).left) →
      Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u, u}
        (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
        (commRestrictModule B S hS p hp (etaleTopology B) (etaleTopology_le_topology B) F.val)
        e.op) := by
    rintro x₁ x₂ e ⟨j, z, ⟨α⟩⟩ h₁ h₂ he
    let G := CatFiberedInGroupoids.homFunctor (f j).hom
    obtain ⟨w₂, -, ι₂, -⟩ := exists_iso_homFunctor_obj_comp_map B S hS (f j) α
    obtain ⟨w₁, δ, ι₁, hδ⟩ := exists_iso_homFunctor_obj_comp_map B S hS (f j) (e ≫ ι₂.hom)
    have hGδ : G.map δ = ι₁.inv ≫ e ≫ ι₂.hom := by
      rw [← hδ, Iso.inv_hom_id_assoc]
    have hiso : ∀ {a b : 𝒳.val.val.obj} (i : a ⟶ b) [IsIso i],
        IsIso (B.inclusion.map (p.map i).left) := fun i _ =>
      inferInstanceAs (IsIso ((p ⋙ Over.forget (B.obj hS) ⋙ B.inclusion).map i))
    have hflatδ : Flat (B.inclusion.map (p.map (G.map δ)).left) := by
      rw [hGδ, p.map_comp, p.map_comp, Over.comp_left, Over.comp_left, Functor.map_comp,
        Functor.map_comp]
      have := hiso ι₁.inv
      have := hiso ι₂.hom
      infer_instance
    have haff : ∀ {a b : 𝒳.val.val.obj} (i : a ⟶ b) [IsIso i],
        IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj b)) →
        IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj a)) := fun i _ hb => by
      have := hiso i
      have : IsAffine (B.inclusion.obj (p.obj _).left) := hb
      exact IsAffine.of_isIso (B.inclusion.map (p.map i).left)
    have hw₁ := haff ι₁.inv h₁
    have hw₂ := haff ι₂.inv h₂
    have hδb := bijective_restrictionBaseChange_of_isLocallyQuasicoherentWithSheafFlatBaseChange
      B E h S hS (G ⋙ p) (isFiberedInGroupoids_homFunctor_comp B S hS (f j).hom) _ (hlqc j) δ
      hflatδ hw₁ hw₂
    have hGb : Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u, u}
        (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
        (commRestrictModule B S hS p hp (etaleTopology B) (etaleTopology_le_topology B) F.val)
        (G.map δ).op) :=
      (Stacks.PresheafOfModules.bijective_restrictionBaseChange_restrictScalars_pushforward₀_iff G
        (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj
        (structureSheaf B S hS (G ⋙ p) (isFiberedInGroupoids_homFunctor_comp B S hS (f j).hom)
          (etaleTopology B) (etaleTopology_le_topology B)).obj
        (eqToHom (ringStructureSheafCore_obj_eq_comp B S hS p hp G
          (isFiberedInGroupoids_homFunctor_comp B S hS (f j).hom)))
        (fun x => ((eqToIso (ringStructureSheafCore_obj_eq_comp B S hS p hp G
          (isFiberedInGroupoids_homFunctor_comp B S hS (f j).hom))).app x).isIso_hom)
        (commRestrictModule B S hS p hp (etaleTopology B) (etaleTopology_le_topology B) F.val)
        δ.op).mp hδb
    refine (Stacks.PresheafOfModules.bijective_restrictionBaseChange_iff_of_arrowIso
      (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
      (commRestrictModule B S hS p hp (etaleTopology B) (etaleTopology_le_topology B) F.val)
      e.op (G.map δ).op ι₂.inv.op ι₁.inv.op ?_).2 hGb
    rw [← op_comp, ← op_comp, hGδ]
    simp
  exact isLocallyQuasicoherentWithSheafFlatBaseChange_of_bijective_restrictionBaseChange_of_flat
    F.val hFet fun _ _ e h₁ h₂ he =>
      bijective_restrictionBaseChange_of_flat_of_goodCover B S hS p hp F.val hFfppf good hgood
        hcov hcart e h₁ h₂ he

/-- An arrow `g : y ⟶ x` factoring over the base of a lift `α : zz ⟶ x` of `mm` factors through
`α`, so there is an arrow `y ⟶ zz`. -/
private theorem nonempty_hom_of_isHomLift_of_map_eq (𝒳 : AlgebraicStacks.{u, w} B S hS)
    {x zz : 𝒳.val.val.obj} (α : zz ⟶ x) {V : BigFppfOver B S hS}
    (mm : V ⟶ 𝒳.val.val.p.obj x) (hlift : 𝒳.val.val.p.IsHomLift mm α) {y : 𝒳.val.val.obj}
    (g : y ⟶ x) (v : 𝒳.val.val.p.obj y ⟶ V) (hv : 𝒳.val.val.p.map g = v ≫ mm) :
    Nonempty (y ⟶ zz) := by
  have : 𝒳.val.val.p.IsStronglyCartesian mm α :=
    𝒳.val.isFiberedInGroupoids.isStronglyCartesian_homLift mm α
  have hl2 : 𝒳.val.val.p.IsHomLift (𝒳.val.val.p.map g) g := inferInstance
  rw [hv] at hl2
  obtain ⟨c, -, -⟩ :=
    Functor.IsStronglyCartesian.universal_property 𝒳.val.val.p mm α v (v ≫ mm) rfl g
  exact ⟨c⟩

/-- **Stacks 07AQ, part (2).** Let `f j : 𝒵 j ⟶ 𝒳` be a family of flat and locally finitely
presented 1-morphisms of algebraic stacks with `|𝒳| = ⋃ j, |f j|(|𝒵 j|)`, and let `F` be a sheaf
of `𝒪_𝒳`-modules on `𝒳_fppf`. If every inverse image `f j^{-1} F` lies in `LQCoh^fbc(𝒪_{𝒵 j})`,
then `F` lies in `LQCoh^fbc(𝒪_𝒳)`.

Membership is read with the flat base change property of Stacks 0762 for the pullback of
sheaves (`IsLocallyQuasicoherentWithSheafFlatBaseChange`), as in part (1)
(`isLocallyQuasicoherentWithSheafFlatBaseChange_of_isSmooth_jointlySurjective`). By the fppf-local
factorization of **Stacks 07AN** (`exists_fppfCovering_family_fibre_lift`) every object of `𝒳` is
covered, for the fppf topology, by objects mapping to images of objects of the `𝒵 j`. -/
theorem locallyQuasicoherentSheafFlatBaseChangeFppfModules_of_isFlat_isLfp_jointlySurjective
    {J : Type v} {𝒵 : J → AlgebraicStacks.{u, w} B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : ∀ j, 𝒵 j ⟶ 𝒳)
    (hflat : ∀ j, AlgebraicStacks.IsFlat B S hS (f j))
    (hlfp : ∀ j, AlgebraicStacks.IsLocallyOfFinitePresentation B S hS (f j))
    (hjs : (Set.univ : Set (AlgebraicStacks.points B S hS 𝒳)) =
      ⋃ j, Set.range (AlgebraicStacks.pointsMap B S hS (f j)))
    (F : fppfModules B S hS 𝒳)
    (hlqc : ∀ j, IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, _, _, u} B E h S hS
      (CatFiberedInGroupoids.homFunctor (f j).hom ⋙ 𝒳.val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS (f j).hom)
      ((stackModulePresheafPullback.{u, w, u} B S hS (f j)).obj F.val)) :
    lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳 F := by
  classical
  set p := 𝒳.val.val.p with hpdef
  have hp := 𝒳.val.isFiberedInGroupoids
  have : p.IsFibered := hp.isFibered
  refine locallyQuasicoherentSheafFlatBaseChangeFppfModules_of_fppfLocal_image B E h S hS f F hlqc
    fun x => ?_
  obtain ⟨I, W, m, a, hflat', hlfp', hcov, hl⟩ :=
    exists_fppfCovering_family_fibre_lift B S hS f hflat hlfp hjs (p.obj x)
      (Functor.Fiber.mk rfl)
  refine ⟨_, Functor.functorPullback_mem_inheritedTopology p (B.topology.over (B.obj hS)) x
    (mem_topology_of_family B S hS W m hflat' hlfp' hcov), ?_⟩
  intro y g hg
  obtain ⟨i, v, hv⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg
  obtain ⟨z, α, hα⟩ := hl i
  obtain ⟨c⟩ := nonempty_hom_of_isHomLift_of_map_eq B S hS 𝒳 α _ hα g v hv
  exact ⟨a i, z, ⟨c⟩⟩

section Atlas

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- The objects in the image of the 1-morphism `x : (Sch/U) → 𝒳` of an object `x` (Stacks 004B)
map to `x`: they are the chosen lifts of `x`. -/
theorem nonempty_homFunctor_objectStackMap_obj_hom (x : 𝒳.val.val.obj)
    (z : (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x)).val.val.obj) :
    Nonempty ((CatFiberedInGroupoids.homFunctor (objectStackMap B S hS 𝒳 x).hom).obj z ⟶ x) :=
  ⟨(Functor.TwoYoneda.chosenLift 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (𝒳.val.val.p.obj x)
    (Functor.Fiber.mk (a := x) rfl) z).φ⟩

/-- An object `x` maps to the image under its 1-morphism `x : (Sch/U) → 𝒳` of the final object
`U / U`: the chosen lift there lies over an identity, hence is an isomorphism onto `x`. -/
theorem nonempty_hom_homFunctor_objectStackMap_obj (x : 𝒳.val.val.obj) :
    Nonempty (x ⟶ (CatFiberedInGroupoids.homFunctor (objectStackMap B S hS 𝒳 x).hom).obj
      (Over.mk (𝟙 (𝒳.val.val.p.obj x)))) := by
  let L := Functor.TwoYoneda.chosenLift 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    (𝒳.val.val.p.obj x) (Functor.Fiber.mk (a := x) rfl) (Over.mk (𝟙 (𝒳.val.val.p.obj x)))
  have : IsIso (Over.mk (𝟙 (𝒳.val.val.p.obj x))).hom := by
    change IsIso (𝟙 _)
    infer_instance
  have := L.isStronglyCartesian
  have : IsIso L.φ :=
    Functor.IsStronglyCartesian.isIso_of_base_isIso 𝒳.val.val.p
      (Over.mk (𝟙 (𝒳.val.val.p.obj x))).hom L.φ
  exact ⟨(asIso L.φ).inv⟩

/-- **Stacks 07AQ (2) for the family of an fppf covering of an atlas object.** Let `x₀` be an
object of `𝒳` whose 1-morphism `x₀ : (Sch/U₀) → 𝒳` is smooth and surjective, and `g j : y j ⟶ x₀`
arrows lying over a jointly surjective family of flat, locally finitely presented morphisms of
schemes. If the inverse image of the sheaf of modules `F` on `𝒳_fppf` along every
`y j : (Sch/U_j) → 𝒳` lies in `LQCoh^fbc`, then `F` lies in `LQCoh^fbc(𝒪_𝒳)`.

Every object of `𝒳` maps, étale-locally, to `x₀` (Stacks 06XH (2) for the smooth surjective
`x₀`), and an object mapping to `x₀` is covered, for the fppf topology, by objects mapping to
some `y j`; those map to the image of `U_j / U_j` under `y j`. -/
theorem locallyQuasicoherentSheafFlatBaseChangeFppfModules_of_flatLfp_cover_of_atlas
    (x₀ : 𝒳.val.val.obj) (hsm : AlgebraicStacks.IsSmooth B S hS (objectStackMap B S hS 𝒳 x₀))
    (hsurj : IsSurjective B S hS (objectStackMap B S hS 𝒳 x₀))
    {J : Type v} (y : J → 𝒳.val.val.obj) (g : ∀ j, y j ⟶ x₀)
    (hflat : ∀ j, Flat ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map (g j))))
    (hlfp : ∀ j, LocallyOfFinitePresentation
      ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map (g j))))
    (hjs : ∀ t, ∃ j s, (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map (g j)) s = t)
    (F : fppfModules B S hS 𝒳)
    (hF : ∀ j, IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, _, _, u} B E h S hS
      (CatFiberedInGroupoids.homFunctor (objectStackMap B S hS 𝒳 (y j)).hom ⋙ 𝒳.val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS _)
      ((stackModulePresheafPullback.{u, w, u} B S hS (objectStackMap B S hS 𝒳 (y j))).obj
        F.val)) :
    lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳 F := by
  classical
  set p := 𝒳.val.val.p with hpdef
  have hp := 𝒳.val.isFiberedInGroupoids
  have : p.IsFibered := hp.isFibered
  have hdown : Sieve.ofArrows (fun j => p.obj (y j)) (fun j => p.map (g j)) ∈
      B.topology.over (B.obj hS) (p.obj x₀) := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    change Sieve.generate (Presieve.ofArrows (fun j => (p.obj (y j)).left)
      (fun j => (p.map (g j)).left)) ∈ B.topology (p.obj x₀).left
    refine Precoverage.generate_mem_toGrothendieck ?_
    rw [bigFppfPrecoverage_eq_comap B, Precoverage.mem_comap_iff, Presieve.map_ofArrows]
    refine (Scheme.ofArrows_mem_precoverage_iff _).mpr ⟨fun t => ?_, fun j => ⟨hflat j, hlfp j⟩⟩
    obtain ⟨j, s, hs⟩ := hjs t
    exact ⟨j, s, hs⟩
  have hx₀ : ∀ ⦃c : 𝒳.val.val.obj⦄ (β : c ⟶ x₀), ∃ R : Sieve c,
      R ∈ BigFppfOver.associatedTopology B S hS p .fppf c ∧
        ∀ ⦃d : 𝒳.val.val.obj⦄ (k : d ⟶ c), R k → ∃ j, Nonempty (d ⟶ y j) := by
    intro c β
    refine ⟨_, GrothendieckTopology.pullback_stable _ β
      (Functor.functorPullback_mem_inheritedTopology p (B.topology.over (B.obj hS)) x₀ hdown),
      fun d k hk => ?_⟩
    obtain ⟨j, v, hv⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hk
    exact ⟨j, nonempty_hom_of_isHomLift_of_map_eq B S hS 𝒳 (g j) (p.map (g j)) inferInstance
      (k ≫ β) v hv⟩
  have hjs₀ : (Set.univ : Set (AlgebraicStacks.points B S hS 𝒳)) =
      ⋃ _ : PUnit.{v + 1}, Set.range (AlgebraicStacks.pointsMap B S hS
        (objectStackMap B S hS 𝒳 x₀)) := by
    rw [Set.iUnion_const]
    exact (Set.range_eq_univ.2 hsurj).symm
  refine locallyQuasicoherentSheafFlatBaseChangeFppfModules_of_fppfLocal_image B E h S hS
    (fun j => objectStackMap B S hS 𝒳 (y j)) F hF fun x => ?_
  obtain ⟨I, W, e, a, hetale, hcovW, hlift⟩ :=
    exists_etaleCovering_family_fibre_lift B S hS (fun _ : PUnit.{v + 1} =>
      objectStackMap B S hS 𝒳 x₀) (fun _ => hsm) hjs₀ (p.obj x) (Functor.Fiber.mk rfl)
  choose zz α hα using hlift
  let R : Sieve x :=
    { arrows := fun z _ => ∃ (j : J) (w₀ : (schemeStack.{u, w} B S hS
          (p.obj (y j))).val.val.obj),
        Nonempty (z ⟶ (CatFiberedInGroupoids.homFunctor (objectStackMap B S hS 𝒳 (y j)).hom).obj
          w₀)
      downward_closed := fun {_ _ _} ⟨j, w₀, ⟨b⟩⟩ k => ⟨j, w₀, ⟨k ≫ b⟩⟩ }
  refine ⟨R, ?_, fun _ _ hg => hg⟩
  refine (BigFppfOver.associatedTopology B S hS p .fppf).transitive
    (Functor.functorPullback_mem_inheritedTopology p (B.topology.over (B.obj hS)) x
      (mem_topology_of_family B S hS W e (fun i => by have := hetale i; infer_instance)
        (fun i => by have := hetale i; infer_instance) hcovW)) _ ?_
  intro c gc hgc
  obtain ⟨i, v, hv⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hgc
  obtain ⟨d⟩ := nonempty_hom_of_isHomLift_of_map_eq B S hS 𝒳 (α i) _ (hα i) gc v hv
  obtain ⟨b⟩ := nonempty_homFunctor_objectStackMap_obj_hom B S hS 𝒳 x₀ (zz i)
  obtain ⟨R', hR', hR'y⟩ := hx₀ (d ≫ b)
  refine (BigFppfOver.associatedTopology B S hS p .fppf).superset_covering ?_ hR'
  intro d' k hk
  obtain ⟨j, ⟨c'⟩⟩ := hR'y k hk
  obtain ⟨t⟩ := nonempty_hom_homFunctor_objectStackMap_obj B S hS 𝒳 (y j)
  exact ⟨j, _, ⟨c' ≫ t⟩⟩

end Atlas

end AlgebraicGeometry.Stack
