module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeSheafUnit
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeSheafSmoothLocal
public import StacksFrontier.AlgebraicGeometry.Stacks.PresentationAlongFunctor
public import StacksFrontier.AlgebraicGeometry.Stacks.CartesianLocallyQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.ChosenEtalePrecoverage
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.StandardCoverings
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Comp

/-!
# Modules cartesian between affine objects have the flat base change property

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and `F` a sheaf of modules on the
fppf site of `𝒳` which is cartesian between affine objects: for every arrow `y ⟶ x` of `𝒳` lying
over a morphism of affine schemes, `𝒪(y) ⊗_{𝒪(x)} F(x) ⟶ F(y)` is bijective (for instance a
quasi-coherent module,
`AlgebraicGeometry.Stack.isCartesianBetweenAffines_of_isQuasicoherentOnSite`). This file proves
that `F`, read as an étale sheaf of modules, has the flat base change property of **Stacks 0762**
in the source's reading on sheaves
(`AlgebraicGeometry.Stack.HasFlatBaseChangePropertySheafUnivLE`).

## The argument

The flat base change property is étale local
(`AlgebraicGeometry.Stack.hasFlatBaseChangePropertySheaf_of_etaleLocal`), and every object of `𝒳`
is covered, by arrows over étale morphisms which are jointly surjective, by objects `z` lying over
affine schemes (`AlgebraicGeometry.Stack.exists_affine_etale_ofArrows`). So it suffices that the
inverse image of `F` to the slice `𝒳/z`, itself a category fibred in groupoids over the schemes,
has the property. Over an affine `z` that inverse image has a global presentation
`⊕ 𝒪 ⟶ ⊕ 𝒪 ⟶ F|_{𝒳/z} ⟶ 0` on the étale site of `𝒳/z`, with generators all of `F(z)` and
relations all the relations among them, because `F` is cartesian along every arrow into `z`
between affine objects and affine objects cover. A module with a global presentation has the flat
base change property: the structure sheaf has it
(`AlgebraicGeometry.Stack.hasFlatBaseChangePropertySheaf_unit`), and the property is stable under
colimits (Stacks 0764 (4)).

## Main results

* `AlgebraicGeometry.Stack.exists_affine_etale_ofArrows`: an object of a category fibred in
  groupoids is covered, for the étale topology, by objects over affine schemes, along arrows over
  étale morphisms which are jointly surjective.
* `AlgebraicGeometry.Stack.hasFlatBaseChangePropertySheaf_of_isPresentedByGlobalSections`: a
  module with a global presentation has the flat base change property.
* `AlgebraicGeometry.Stack.hasFlatBaseChangePropertySheaf_of_isCartesianBetweenAffines`: an fppf
  module cartesian between affine objects has the flat base change property as an étale module.

## References

* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 0764](https://stacks.math.columbia.edu/tag/0764)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

section Cover

variable {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)

/-- **An object of the big fppf site is covered by affine schemes along étale morphisms**: the
affine open covering of the scheme, realised in the site by Stacks 03WX, is a family of étale
morphisms from affine schemes which is jointly surjective and an étale covering family. -/
private theorem exists_affine_etale_presieve₀_mem_etalePrecoverage (T : B.Schemes) :
    ∃ V : PreZeroHypercover.{u + 1} T,
      (∀ j, IsAffine (B.inclusion.obj (V.X j))) ∧ (∀ j, Etale (B.inclusion.map (V.f j))) ∧
      (∀ t : B.inclusion.obj T, ∃ j, t ∈ Set.range (B.inclusion.map (V.f j))) ∧
      V.presieve₀ ∈ etalePrecoverage B T := by
  classical
  let U := (B.inclusion.obj T).affineOpenCover.openCover
  obtain ⟨V, hV, ⟨α, hα⟩, ⟨β, hβ⟩⟩ :=
    exists_isCovering_tautologicallyEquivalent_openCover B T U
  have hVaff : ∀ j, IsAffine (B.inclusion.obj (V.X j)) := by
    intro j
    obtain ⟨e, -⟩ := hβ j
    have : IsAffine (U.X (β j)) := isAffine_Spec _
    exact @IsAffine.of_isIso _ _ e.hom e.isIso_hom inferInstance
  have hVet : ∀ j, Etale (B.inclusion.map (V.f j)) := by
    intro j
    obtain ⟨e, he⟩ := hβ j
    show Etale ((V.map B.inclusion).f j)
    rw [← he]
    infer_instance
  have hVsurj : ∀ t : B.inclusion.obj T,
      ∃ j, t ∈ Set.range (B.inclusion.map (V.f j)) := by
    intro t
    obtain ⟨s, hs⟩ := U.covers t
    obtain ⟨e, he⟩ := hα (U.idx t)
    refine ⟨α (U.idx t), e.hom s, ?_⟩
    show ((V.map B.inclusion).f (α (U.idx t))) (e.hom s) = t
    rw [← Scheme.Hom.comp_apply, he, hs]
  exact ⟨V, hVaff, hVet, hVsurj, V, rfl, hV,
    (Scheme.presieve₀_mem_precoverage_iff (P := @Etale) (V.map B.inclusion)).2 ⟨hVsurj, hVet⟩⟩

/-- **An object of a category fibred in groupoids is covered, for the étale topology, by objects
over affine schemes**, along arrows lying over étale morphisms which are jointly surjective onto
the scheme below the object. The family is the cartesian lift of an affine open covering of that
scheme, which is a chosen étale covering family of the big site by Stacks 03WX. -/
theorem exists_affine_etale_ofArrows (hp : p.IsFiberedInGroupoids) (W : 𝒳) :
    ∃ (I : Type (u + 1)) (y : I → 𝒳) (φ : ∀ j, y j ⟶ W),
      (∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj (y j)))) ∧
      (∀ j, Etale (B.inclusion.map (p.map (φ j)).left)) ∧
      (∀ t : B.inclusion.obj (p.obj W).left,
        ∃ j, t ∈ Set.range (B.inclusion.map (p.map (φ j)).left)) ∧
      Sieve.ofArrows y φ ∈ associatedTopology B S hS p (etaleTopology B) W := by
  classical
  obtain ⟨V, hVaff, hVet, hVsurj, hpre⟩ :=
    exists_affine_etale_presieve₀_mem_etalePrecoverage B (p.obj W).left
  let Vobj (j : V.I₀) : BigFppfOver B S hS := Over.mk (V.f j ≫ (p.obj W).hom)
  let vmap (j : V.I₀) : Vobj j ⟶ p.obj W := Over.homMk (V.f j)
  have hBcover : Sieve.ofArrows Vobj vmap ∈ (etaleTopology B).over (B.obj hS) (p.obj W) := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    show Sieve.ofArrows V.X V.f ∈ etaleTopology B (p.obj W).left
    simpa [PreZeroHypercover.presieve₀] using Precoverage.generate_mem_toGrothendieck hpre
  choose y φ hφ using fun j => hp.exists_lift (vmap j) W rfl
  have := hφ
  have hdom : ∀ j, p.obj (y j) = Vobj j := fun j => IsHomLift.domain_eq p (vmap j) (φ j)
  have hmap : ∀ j, p.map (φ j) = eqToHom (hdom j) ≫ vmap j := fun j => by
    conv_rhs => rw [IsHomLift.fac p (vmap j) (φ j)]
    simp
  have hvmapmem : ∀ j, (Sieve.ofArrows (fun k => p.obj (y k)) fun k => p.map (φ k)) (vmap j) := by
    intro j
    refine (Sieve.mem_ofArrows_iff _ _ _).2 ⟨j, eqToHom (hdom j).symm, ?_⟩
    rw [hmap j]
    simp
  have : p.IsFibered := hp.isFibered
  refine ⟨V.I₀, y, φ, fun j => ?_, fun j => ?_, fun t => ?_, ?_⟩
  · rw [hdom j]
    exact hVaff j
  · rw [hmap j, Over.comp_left, Functor.map_comp, Over.eqToHom_left]
    exact (MorphismProperty.cancel_left_of_respectsIso @Etale _ _).2 (hVet j)
  · obtain ⟨j, s, hs⟩ := hVsurj t
    refine ⟨j, (inv (B.inclusion.map (eqToHom (congrArg Over.left (hdom j))))) s, ?_⟩
    rwa [hmap j, Over.comp_left, Functor.map_comp, Over.eqToHom_left, ← Scheme.Hom.comp_apply,
      IsIso.inv_hom_id_assoc]
  · refine (Functor.isInheritedTopology_inheritedTopology p
      ((etaleTopology B).over (B.obj hS)) y φ fun j => hp.isStronglyCartesian (φ j)).2 ?_
    refine ((etaleTopology B).over (B.obj hS)).superset_covering ?_ hBcover
    intro Z g hg
    obtain ⟨j, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hg
    exact (Sieve.ofArrows (fun k => p.obj (y k)) fun k => p.map (φ k)).downward_closed
      (hvmapmem j) a

end Cover

section Presented

variable {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- **A module with a global presentation has the flat base change property** (Stacks 0762), in
the source's reading on sheaves: it is a cokernel of a map between two coproducts of copies of
the structure sheaf, the structure sheaf has the property
(`AlgebraicGeometry.Stack.hasFlatBaseChangePropertySheaf_unit`), and the property is stable under
colimits (Stacks 0764 (4),
`AlgebraicGeometry.Stack.hasFlatBaseChangePropertySheaf_of_isColimit`). -/
theorem hasFlatBaseChangePropertySheaf_of_isPresentedByGlobalSections
    {N : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B))}
    (hN : N.IsPresentedByGlobalSections) :
    HasFlatBaseChangePropertySheafUnivLE.{u, v, w, u} B E h S hS p hp N := by
  obtain ⟨I, K, P, Q, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hc⟩⟩ := hN
  have hO : HasFlatBaseChangePropertySheafUnivLE.{u, v, w, u} B E h S hS p hp
      (SheafOfModules.unit (ringStructureSheafCore B S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B))) :=
    hasFlatBaseChangePropertySheaf_unit B E h S hS p hp
  have hK : ∀ j, HasFlatBaseChangePropertySheafUnivLE.{u, v, w, u} B E h S hS p hp
      ((parallelPair a 0).obj j) := by
    rintro (_ | _)
    · exact hasFlatBaseChangePropertySheaf_of_isColimit B E h S hS p hp hQ fun _ => hO
    · exact hasFlatBaseChangePropertySheaf_of_isColimit B E h S hS p hp hP fun _ => hO
  intro x y φ hφ
  exact hasFlatBaseChangePropertySheaf_of_isColimit B E h S hS p hp hc hK φ hφ

end Presented

section Cartesian

variable {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- The slice `𝒳/z` of a category fibred in groupoids over the schemes is again one, through the
forgetful functor. -/
theorem isFiberedInGroupoids_overForget_comp_of_isFiberedInGroupoids (hp : p.IsFiberedInGroupoids)
    (z : 𝒳) :
    (Over.forget z ⋙ p).IsFiberedInGroupoids :=
  Functor.IsFiberedInGroupoids.comp _ _ (Functor.IsFiberedInGroupoids.over_forget z) hp

/-- An fppf sheaf of modules on `𝒳` read as an étale sheaf of modules: the underlying presheaf of
modules is unchanged. -/
abbrev etaleModuleOfFppf
    (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp B.topology le_rfl)) :
    SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)) :=
  ⟨F.val, F.isSheaf.of_le (associatedTopology_etale_le_fppf B S hS p)⟩

/-- **Along an arrow between affine objects, every section of a module cartesian between affine
objects is a combination of restrictions of sections over the target.** -/
private theorem exists_finsupp_sum_smul_of_isCartesianBetweenAffines
    (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp B.topology le_rfl))
    (hF : IsCartesianBetweenAffines hp F) {x y : 𝒳} (g : y ⟶ x)
    (hx : IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj x))
    (hy : IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj y)) (m : F.val.obj (op y)) :
    letI := fibredSectionsModule hp F y
    ∃ c : F.val.obj (op x) →₀ fibredSectionRing B S hS p y,
      (c.sum fun i r ↦ r • (show F.val.obj (op y) from F.val.map g.op i)) = m := by
  let := fibredSectionAlgebra (B := B) (S := S) (hS := hS) (p := p) g
  let := fibredSectionsModule hp F x
  let := fibredSectionsModule hp F y
  let := fibredSectionsModuleOver hp F g
  have : IsScalarTower (fibredSectionRing B S hS p x) (fibredSectionRing B S hS p y)
      (F.val.obj (op y)) := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  exact Module.BaseChange.exists_finsupp_of_surjective_liftBaseChange
    (fibredSectionsRestrict hp F g) (hF g hx hy).2 m

/-- **Along an arrow `k = g ≫ f` between affine objects, a relation over `w` among the
restrictions of the sections over `x` of a module cartesian between affine objects restricts to a
combination of the relations among those sections.** -/
private theorem exists_finsupp_relations_of_isCartesianBetweenAffines
    (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp B.topology le_rfl))
    (hF : IsCartesianBetweenAffines hp F) {x y w : 𝒳} (f : w ⟶ x) (g : y ⟶ w) (k : y ⟶ x)
    (hk : k = g ≫ f) (hx : IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj x))
    (hy : IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj y))
    (c : F.val.obj (op x) →₀ fibredSectionRing B S hS p w)
    (hc : letI := fibredSectionsModule hp F w
      (c.sum fun i r ↦ r • (show F.val.obj (op w) from F.val.map f.op i)) = 0) :
    letI := fibredSectionAlgebra (B := B) (S := S) (hS := hS) (p := p) k
    letI := fibredSectionsModule hp F x
    ∃ d : Module.BaseChange.Relations (fibredSectionRing B S hS p x) (F.val.obj (op x)) →₀
        fibredSectionRing B S hS p y,
      c.mapRange (fibredSectionRestrict g) (map_zero _) = d.sum fun k r ↦
        r • k.1.mapRange (algebraMap (fibredSectionRing B S hS p x) (fibredSectionRing B S hS p y))
          (map_zero _) := by
  subst hk
  let := fibredSectionAlgebra (B := B) (S := S) (hS := hS) (p := p) (g ≫ f)
  let := fibredSectionsModule hp F x
  let := fibredSectionsModule hp F y
  let := fibredSectionsModule hp F w
  let := fibredSectionsModuleOver hp F (g ≫ f)
  have : IsScalarTower (fibredSectionRing B S hS p x) (fibredSectionRing B S hS p y)
      (F.val.obj (op y)) := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  refine Module.BaseChange.exists_finsupp_relations_of_bijective_liftBaseChange
    (fibredSectionsRestrict hp F (g ≫ f)) (hF (g ≫ f) hx hy) _ ?_
  refine Eq.trans (Finset.sum_congr rfl fun i _ ↦ congrArg (_ • ·) ?_)
    ((Stacks.SheafOfModules.FreeSheafification.map_finsupp_sum_smul F.val g.op c
      fun i ↦ (show F.val.obj (op w) from F.val.map f.op i)).symm.trans
      ((congrArg (fun m ↦ F.val.map g.op m) hc).trans (map_zero _)))
  show F.val.map (g ≫ f).op i = F.val.map g.op (F.val.map f.op i)
  rw [op_comp]
  exact F.val.map_comp_apply _ _ i

/-- **Over an affine object, the inverse image of a module cartesian between affine objects to the
slice has a global presentation on the étale site**, by generators all the sections over `z` and
relations all the relations among them: every object of `𝒳/z` is covered by affine objects, along
whose arrows to `z` the module is cartesian. -/
theorem isPresentedByGlobalSections_modulePullback_overForget
    (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp B.topology le_rfl))
    (hF : IsCartesianBetweenAffines hp F) {z : 𝒳}
    (hz : IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj z)) :
    ((modulePullback B S hS (Over.forget z ⋙ p) p
        (isFiberedInGroupoids_overForget_comp_of_isFiberedInGroupoids B S hS p hp z)
      hp (Over.forget z) rfl (etaleTopology B) (etaleTopology_le_topology B)).obj
        (etaleModuleOfFppf B S hS p hp F)).IsPresentedByGlobalSections := by
  classical
  let q := Over.forget z ⋙ p
  have hq : q.IsFiberedInGroupoids :=
    isFiberedInGroupoids_overForget_comp_of_isFiberedInGroupoids B S hS p hp z
  have := hasSheafify_etaleAssociatedTopology B S hS q hq
  have := wEqualsLocallyBijective_etaleAssociatedTopology B S hS q hq
  have : p.IsFibered := hp.isFibered
  have : q.IsFibered := hq.isFibered
  have := ((hp.isFibredOneMorphism (show Over.forget z ⋙ p = q from rfl))
    |>.isContinuous_and_isCocontinuous_inheritedTopology ((etaleTopology B).over (B.obj hS))).1
  let Fn : Over z ⥤ 𝒳 := Over.forget z
  let t : Over z := Over.mk (𝟙 z)
  have ht : IsTerminal t := Over.mkIdTerminal
  let M := etaleModuleOfFppf B S hS p hp F
  have hR : (Fn.sheafPushforwardContinuous RingCat.{u}
      (associatedTopology B S hS q (etaleTopology B))
      (associatedTopology B S hS p (etaleTopology B))).obj
        (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)) =
      ringStructureSheafCore B S hS q hq (etaleTopology B) (etaleTopology_le_topology B) := rfl
  let := fibredSectionsModule hp F z
  refine
    (Stacks.SheafOfModules.FreeSheafification.isPresentedByGlobalSections_pushforward_of_terminal
      Fn hR M t ht (F.val.obj (op z))
      (Module.BaseChange.Relations (fibredSectionRing B S hS p z) (F.val.obj (op z)))
      (fun i ↦ i) (fun k ↦ k.1) (fun k ↦ k.2) ?_ ?_).1
  · intro V x
    obtain ⟨Ic, y, φ, haff, -, -, hcov⟩ := exists_affine_etale_ofArrows B S hS q hq V
    refine ⟨Presieve.ofArrows y φ, hcov, ?_⟩
    rintro W g ⟨j⟩
    exact exists_finsupp_sum_smul_of_isCartesianBetweenAffines B S hS p hp F hF
      (Fn.map (ht.from (y j))) hz (haff j) (F.val.map (Fn.map (φ j)).op x)
  · intro V c hc
    obtain ⟨Ic, y, φ, haff, -, -, hcov⟩ := exists_affine_etale_ofArrows B S hS q hq V
    refine ⟨Presieve.ofArrows y φ, hcov, ?_⟩
    rintro W g ⟨j⟩
    exact exists_finsupp_relations_of_isCartesianBetweenAffines B S hS p hp F hF
      (Fn.map (ht.from V)) (Fn.map (φ j)) (Fn.map (ht.from (y j)))
      ((congrArg Fn.map (ht.hom_ext (ht.from (y j)) (φ j ≫ ht.from V))).trans (Fn.map_comp _ _))
      hz (haff j) c hc

/-- **A sheaf of modules on the fppf site of `𝒳` which is cartesian between affine objects has
the flat base change property** of Stacks 0762 as an étale sheaf of modules, in the source's
reading on sheaves. The property is étale local, objects over affine schemes cover, and over an
affine `z` the inverse image of the module to `𝒳/z` has a global presentation. -/
theorem hasFlatBaseChangePropertySheaf_of_isCartesianBetweenAffines
    (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp B.topology le_rfl))
    (hF : IsCartesianBetweenAffines hp F) :
    HasFlatBaseChangePropertySheafUnivLE.{u, v, w, u} B E h S hS p hp
      (etaleModuleOfFppf B S hS p hp F) := by
  refine hasFlatBaseChangePropertySheaf_of_etaleLocal B E h S hS p hp
    (ι := {z : 𝒳 // IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj z)})
    (fun i ↦ Over.forget i.1)
    (fun i ↦ isFiberedInGroupoids_overForget_comp_of_isFiberedInGroupoids B S hS p hp i.1)
    (fun y ↦ ?_) _ (fun i ↦ ?_)
  · obtain ⟨I, yy, φ, haff, het, hsurj, -⟩ := exists_affine_etale_ofArrows B S hS p hp y
    exact ⟨I, fun j ↦ ⟨yy j, haff j⟩, fun j ↦ Over.mk (𝟙 (yy j)), φ, het, hsurj⟩
  · exact hasFlatBaseChangePropertySheaf_of_isPresentedByGlobalSections B E h S hS
      (Over.forget i.1 ⋙ p)
      (isFiberedInGroupoids_overForget_comp_of_isFiberedInGroupoids B S hS p hp i.1)
      (isPresentedByGlobalSections_modulePullback_overForget B S hS p hp F hF i.2)

end Cartesian

end AlgebraicGeometry.Stack

end
