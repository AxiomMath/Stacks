module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatCartesianFppfDescentLargeSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeAffineChartLocality
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeFlatLocal

/-!
# Stacks 07AQ (2) at module universe `u + 1`

Let `f j : 𝒵 j ⟶ 𝒳` be a family of flat and locally finitely presented 1-morphisms of algebraic
stacks with `|𝒳| = ⋃ j, |f j|(|𝒵 j|)`, and let `F` be a sheaf of `𝒪_𝒳`-modules on `𝒳_fppf` with
sections in `Type (u + 1)`, one universe above the structure sheaf: the universe of the modules of
Stacks 07AV, 07BC and 07BE. **Stacks 07AQ** part (2) says: if every `f j^{-1} F` lies in
`LQCoh^fbc(𝒪_{𝒵 j})`, then `F` lies in `LQCoh^fbc(𝒪_𝒳)`. This file proves it at that universe, for
the faithful class (`AlgebraicGeometry.Stack.AlgebraicStacks.sheafFlatBaseChangeModuleRule`, the
flat base change property of Stacks 0762 read with the pullback of sheaves); the universe-`u`
statement is
`Stack.locallyQuasicoherentSheafFlatBaseChangeFppfModules_of_isFlat_isLfp_jointlySurjective`.

## The argument

It is the argument of the universe-`u` file, run through the cartesian property over flat arrows
between objects over affine schemes, which characterizes the faithful class at large module
universes:

* a module in the faithful class is cartesian over flat arrows between affine objects
  (`AlgebraicGeometry.Stack.bijective_restrictionBaseChange_of_flat_freeModuleUniverse`, the
  direction (⇒) of Stacks 07B1's characterization); applied to `f j^{-1} F` this makes `F`
  cartesian over the flat arrows between affine objects whose target maps to an image of `f j`
  (`AlgebraicGeometry.Stack.exists_iso_homFunctor_obj_comp_map`);
* those targets cover `𝒳` for the fppf topology (Stacks 07AN), and the cartesian property
  descends along such coverings
  (`Stack.bijective_restrictionBaseChange_of_flat_of_goodCover_freeModuleUniverse`);
* an étale sheaf cartesian over all flat arrows between affine objects lies in the faithful class
  (`Stack.isLocallyQuasicoherentWithSheafFlatBaseChangeUnivLE_of_isCartesianOnFlatAffineArrows`).

## Main results

* `Stack.AlgebraicStacks.sheafFlatBaseChangeModuleRule_of_fppfLocal_image`: the common core,
  fppf-local factorization through the images of the `f j`.
* `Stack.AlgebraicStacks.sheafFlatBaseChangeModuleRule_of_isFlat_isLfp_jointlySurjective`:
  **Stacks 07AQ** (2) at module universe `u + 1`.
* `Stack.AlgebraicStacks.sheafFlatBaseChangeModuleRule_of_flatLfp_cover_of_atlas`: the form in
  which the reduction of Stacks 07B3 (2) at module universe `u + 1` consumes it.

## References

* [Stacks Project, Tag 07AQ](https://stacks.math.columbia.edu/tag/07AQ)
* [Stacks Project, Tag 07AN](https://stacks.math.columbia.edu/tag/07AN)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 07B3](https://stacks.math.columbia.edu/tag/07B3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- An arrow into `x` whose image factors through the image of a strongly cartesian lift `α`
of `mm` factors through `α`. -/
private theorem nonempty_hom_of_map_eq_comp {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {x zz : 𝒳.val.val.obj} (α : zz ⟶ x) {V : BigFppfOver B S hS}
    (mm : V ⟶ 𝒳.val.val.p.obj x) (hlift : 𝒳.val.val.p.IsHomLift mm α) {y : 𝒳.val.val.obj}
    (g : y ⟶ x) (v : 𝒳.val.val.p.obj y ⟶ V) (hv : 𝒳.val.val.p.map g = v ≫ mm) :
    Nonempty (y ⟶ zz) := by
  have hp := 𝒳.val.isFiberedInGroupoids
  have hcart : 𝒳.val.val.p.IsStronglyCartesian mm α := hp.isStronglyCartesian_homLift mm α
  have hl2 : 𝒳.val.val.p.IsHomLift (𝒳.val.val.p.map g) g := inferInstance
  rw [hv] at hl2
  obtain ⟨c, -, -⟩ :=
    Functor.IsStronglyCartesian.universal_property 𝒳.val.val.p mm α v (v ≫ mm) rfl g
  exact ⟨c⟩

/-- **The faithful `LQCoh^fbc` at module universe `u + 1` is fppf-local through the images of a
family of 1-morphisms.** Let `f j : 𝒵 j ⟶ 𝒳` be 1-morphisms of algebraic stacks and `F` a module on
`𝒳_fppf` with sections in `Type (u + 1)` every inverse image `f j^{-1} F` of which lies in
`LQCoh^fbc(𝒪_{𝒵 j})`. If every object of `𝒳` has a covering sieve for the fppf topology all of
whose members have a source mapping to an image of some `f j`, then `F` lies in
`LQCoh^fbc(𝒪_𝒳)`. -/
theorem sheafFlatBaseChangeModuleRule_of_fppfLocal_image
    {J : Type v} {𝒵 : J → AlgebraicStacks.{u, w} B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : ∀ j, 𝒵 j ⟶ 𝒳) (F : fppfModules B S hS 𝒳)
    (hlqc : ∀ j, sheafFlatBaseChangeModuleRule B S hS E h (𝒵 j)
      ((fppfModulePullback B S hS (f j)).obj F))
    (hcov : ∀ x : 𝒳.val.val.obj, ∃ R : Sieve x,
      R ∈ BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf x ∧
        ∀ ⦃z : 𝒳.val.val.obj⦄ (g : z ⟶ x), R g → ∃ (j : J) (w₀ : (𝒵 j).val.val.obj),
          Nonempty (z ⟶ (CatFiberedInGroupoids.homFunctor (f j).hom).obj w₀)) :
    sheafFlatBaseChangeModuleRule B S hS E h 𝒳 F := by
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
      Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u, u + 1}
        (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
        F.val e.op) := by
    rintro x₁ x₂ e ⟨j, z, ⟨α⟩⟩ h₁ h₂ he
    let G := CatFiberedInGroupoids.homFunctor (f j).hom
    obtain ⟨w₂, -, ι₂, -⟩ := exists_iso_homFunctor_obj_comp_map B S hS (f j) α
    obtain ⟨w₁, δ, ι₁, hδ⟩ := exists_iso_homFunctor_obj_comp_map B S hS (f j) (e ≫ ι₂.hom)
    have hGδ : G.map δ = ι₁.inv ≫ e ≫ ι₂.hom := by
      rw [← hδ, Iso.inv_hom_id_assoc]
    have hiso : ∀ {a b : 𝒳.val.val.obj} (i : a ⟶ b) [IsIso i],
        IsIso (B.inclusion.map (p.map i).left) := fun i _ =>
      inferInstanceAs (IsIso ((p ⋙ Over.forget (B.obj hS) ⋙ B.inclusion).map i))
    have hflatδ : Flat (B.inclusion.map ((G ⋙ p).map δ).left) := by
      change Flat (B.inclusion.map (p.map (G.map δ)).left)
      rw [hGδ, p.map_comp, p.map_comp, Over.comp_left, Over.comp_left, Functor.map_comp,
        Functor.map_comp]
      have := hiso ι₁.inv
      have := hiso ι₂.hom
      infer_instance
    have hw₁ : IsAffine (((G ⋙ p) ⋙ BigFppfOver.toScheme B S hS).obj w₁) := by
      have := hiso ι₁.inv
      have : IsAffine (B.inclusion.obj (p.obj x₁).left) := h₁
      exact IsAffine.of_isIso (B.inclusion.map (p.map ι₁.inv).left)
    have hw₂ : IsAffine (((G ⋙ p) ⋙ BigFppfOver.toScheme B S hS).obj w₂) := by
      have := hiso ι₂.inv
      have : IsAffine (B.inclusion.obj (p.obj x₂).left) := h₂
      exact IsAffine.of_isIso (B.inclusion.map (p.map ι₂.inv).left)
    have hpull := (isLocallyQuasicoherentWithSheafFlatBaseChangeUnivLE_modulePullback_iff B E h S
      hS _ (𝒵 j).val.isFiberedInGroupoids p hp G (CatFiberedInGroupoids.homFunctor_comp_p (f j).hom)
      (isFiberedInGroupoids_homFunctor_comp B S hS (f j).hom) F).1 (hlqc j)
    have hGb : Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u,
        u + 1}
        (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
        F.val (G.map δ).op) :=
      bijective_restrictionBaseChange_of_flat_freeModuleUniverse.{u, u + 1, u, u}
        B E h S hS (G ⋙ p) (isFiberedInGroupoids_homFunctor_comp B S hS (f j).hom) _ hpull
        δ hflatδ hw₁ hw₂
    refine
      (Stacks.PresheafOfModules.bijective_restrictionBaseChange_iff_of_arrowIso_freeModuleUniverse.{
        u + 1, u, u, u + 1}
        (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
        F.val e.op (G.map δ).op ι₂.inv.op ι₁.inv.op ?_).2 hGb
    rw [← op_comp, ← op_comp, hGδ]
    simp
  exact isLocallyQuasicoherentWithSheafFlatBaseChangeUnivLE_of_isCartesianOnFlatAffineArrows.{u,
    u + 1, u, u} B E h S hS p hp F.val hFet fun _ _ e he h₁ h₂ =>
      bijective_restrictionBaseChange_of_flat_of_goodCover_freeModuleUniverse.{u, u + 1, u, u}
        B S hS p hp F.val hFfppf good hgood hcov hcart e h₁ h₂ he

/-- **Stacks 07AQ, part (2), at module universe `u + 1`.** Let `f j : 𝒵 j ⟶ 𝒳` be a family of
flat and locally finitely presented 1-morphisms of algebraic stacks with
`|𝒳| = ⋃ j, |f j|(|𝒵 j|)`, and let `F` be a module on `𝒳_fppf` with sections in `Type (u + 1)`.
If every inverse image `f j^{-1} F` lies in `LQCoh^fbc(𝒪_{𝒵 j})`, then `F` lies in
`LQCoh^fbc(𝒪_𝒳)`, for the faithful class (the flat base change property of Stacks 0762 read with
the pullback of sheaves). By the fppf-local factorization of Stacks 07AN
(`AlgebraicGeometry.Stack.exists_fppfCovering_family_fibre_lift`) every object of `𝒳` is covered,
for the fppf topology, by objects mapping to images of objects of the `𝒵 j`, and
`AlgebraicGeometry.Stack.AlgebraicStacks.sheafFlatBaseChangeModuleRule_of_fppfLocal_image`
concludes. -/
theorem sheafFlatBaseChangeModuleRule_of_isFlat_isLfp_jointlySurjective
    {J : Type v} {𝒵 : J → AlgebraicStacks.{u, w} B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : ∀ j, 𝒵 j ⟶ 𝒳)
    (hflat : ∀ j, AlgebraicStacks.IsFlat B S hS (f j))
    (hlfp : ∀ j, AlgebraicStacks.IsLocallyOfFinitePresentation B S hS (f j))
    (hjs : (Set.univ : Set (AlgebraicStacks.points B S hS 𝒳)) =
      ⋃ j, Set.range (AlgebraicStacks.pointsMap B S hS (f j)))
    (F : fppfModules B S hS 𝒳)
    (hlqc : ∀ j, sheafFlatBaseChangeModuleRule B S hS E h (𝒵 j)
      ((fppfModulePullback B S hS (f j)).obj F)) :
    sheafFlatBaseChangeModuleRule B S hS E h 𝒳 F := by
  classical
  set p := 𝒳.val.val.p with hpdef
  have hp := 𝒳.val.isFiberedInGroupoids
  have : p.IsFibered := hp.isFibered
  refine sheafFlatBaseChangeModuleRule_of_fppfLocal_image B E h S hS f F hlqc fun x => ?_
  obtain ⟨I, W, m, a, hflat', hlfp', hcov, hl⟩ :=
    exists_fppfCovering_family_fibre_lift B S hS f hflat hlfp hjs (p.obj x)
      (Functor.Fiber.mk rfl)
  refine ⟨_, Functor.functorPullback_mem_inheritedTopology p (B.topology.over (B.obj hS)) x
    (mem_topology_of_family B S hS W m hflat' hlfp' hcov), ?_⟩
  intro y g hg
  obtain ⟨i, v, hv⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg
  obtain ⟨z, α, hα⟩ := hl i
  obtain ⟨c⟩ := nonempty_hom_of_map_eq_comp B S hS α _ hα g v hv
  exact ⟨a i, z, ⟨c⟩⟩

section Atlas

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- **Stacks 07AQ (2) at module universe `u + 1`, for the family of an fppf covering of an atlas
object.** Let `x₀` be an object of `𝒳` whose 1-morphism `x₀ : (Sch/U₀) → 𝒳` is smooth and
surjective, and `g j : y j ⟶ x₀` arrows lying over a jointly surjective family of flat, locally
finitely presented morphisms of schemes. If the inverse image of the module `F` on `𝒳_fppf`, with
sections in `Type (u + 1)`, along every `y j : (Sch/U_j) → 𝒳` lies in `LQCoh^fbc`, then `F` lies
in `LQCoh^fbc(𝒪_𝒳)`. The universe-`u` statement is
`Stack.locallyQuasicoherentSheafFlatBaseChangeFppfModules_of_flatLfp_cover_of_atlas`, and the
covering argument is the same. -/
theorem sheafFlatBaseChangeModuleRule_of_flatLfp_cover_of_atlas
    (x₀ : 𝒳.val.val.obj) (hsm : AlgebraicStacks.IsSmooth B S hS (objectStackMap B S hS 𝒳 x₀))
    (hsurj : IsSurjective B S hS (objectStackMap B S hS 𝒳 x₀))
    {J : Type v} (y : J → 𝒳.val.val.obj) (g : ∀ j, y j ⟶ x₀)
    (hflat : ∀ j, Flat ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map (g j))))
    (hlfp : ∀ j, LocallyOfFinitePresentation
      ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map (g j))))
    (hjs : ∀ t, ∃ j s, (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map (g j)) s = t)
    (F : fppfModules B S hS 𝒳)
    (hF : ∀ j, sheafFlatBaseChangeModuleRule B S hS E h
      (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj (y j)))
      ((fppfModulePullback B S hS (objectStackMap B S hS 𝒳 (y j))).obj F)) :
    sheafFlatBaseChangeModuleRule B S hS E h 𝒳 F := by
  classical
  set p := 𝒳.val.val.p with hpdef
  have hp := 𝒳.val.isFiberedInGroupoids
  have : p.IsFibered := hp.isFibered
  -- the sieve of arrows out of objects mapping to some `y j` covers `x₀`
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
    exact ⟨j, nonempty_hom_of_map_eq_comp B S hS (g j) (p.map (g j)) inferInstance (k ≫ β) v hv⟩
  -- every object is étale-locally mapped to `x₀`
  have hjs₀ : (Set.univ : Set (AlgebraicStacks.points B S hS 𝒳)) =
      ⋃ _ : PUnit.{v + 1}, Set.range (AlgebraicStacks.pointsMap B S hS
        (objectStackMap B S hS 𝒳 x₀)) := by
    rw [Set.iUnion_const]
    exact (Set.range_eq_univ.2 hsurj).symm
  refine sheafFlatBaseChangeModuleRule_of_fppfLocal_image B E h S hS
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
  obtain ⟨d⟩ := nonempty_hom_of_map_eq_comp B S hS (α i) _ (hα i) gc v hv
  obtain ⟨b⟩ := nonempty_homFunctor_objectStackMap_obj_hom B S hS 𝒳 x₀ (zz i)
  obtain ⟨R', hR', hR'y⟩ := hx₀ (d ≫ b)
  refine (BigFppfOver.associatedTopology B S hS p .fppf).superset_covering ?_ hR'
  intro d' k hk
  obtain ⟨j, ⟨c'⟩⟩ := hR'y k hk
  obtain ⟨t⟩ := nonempty_hom_homFunctor_objectStackMap_obj B S hS 𝒳 (y j)
  exact ⟨j, _, ⟨c' ≫ t⟩⟩

end Atlas

end AlgebraicGeometry.Stack.AlgebraicStacks
