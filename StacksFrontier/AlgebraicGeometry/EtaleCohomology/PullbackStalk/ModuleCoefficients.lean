module

public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointDomination
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.Coefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkIsomorphismCriterion
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SurjectiveMorphismStalkDescent

/-!
# Inverse images and stalks of étale sheaves of modules

Fix a coefficient ring `Λ`. A sheaf of `Λ`-modules on a small étale site has a stalk at every
geometric point, and the two basic facts about those stalks hold for module coefficients exactly
as they do for sets and for abelian groups: the stalk of an inverse image at a geometric point is
the stalk of the sheaf at the image geometric point (Stacks 03Q1), and a map of sheaves which is
surjective on every stalk is locally surjective (Stacks 03PU). Combining them, inverse image
along a surjective morphism of schemes *reflects* epimorphisms of sheaves of modules.

The surjectivity criterion is proved here for an arbitrary concrete coefficient category with the
colimits that form stalks and a forgetful functor preserving them; the module case is the
specialization. The identification of the stalk of an inverse image is already available in that
generality as `AlgebraicGeometry.smallEtalePullbackSheafFiberIso`, so for modules it only has to
be fed the products that build skyscrapers.

A geometric point of the target does *not* in general lift along a surjective morphism `f`; what
is true is that it has the same image point as one of the form `f ∘ x̄`, and the stalk functor
depends only on that image point (Stacks 04FN). This is why the descent step goes through
`AlgebraicGeometry.etaleStalkPresheafFunctorIsoOfEqBase` and not through a lift.

## Main definitions

* `AlgebraicGeometry.etaleStalkFunctorModule` — the stalk at a geometric point, as a functor on
  the sheaves of `Λ`-modules of a small étale site.
* `AlgebraicGeometry.smallEtaleModulePullbackFunctor` — inverse image of sheaves of `Λ`-modules
  along a morphism of the big étale site.

## Main results

* `AlgebraicGeometry.isLocallySurjective_of_surjective_etaleStalkMapOfCoefficients` — Stacks
  03PU for an arbitrary concrete coefficient category, and
  `AlgebraicGeometry.isLocallySurjective_of_surjective_etaleStalkMap_module` for modules.
* `AlgebraicGeometry.smallEtalePullbackStalkIsoModule` — Stacks 03Q1 for module coefficients.
* `AlgebraicGeometry.surjective_etaleStalkMap_of_isLocallySurjective_module` — the converse half
  of Stacks 03PU for module coefficients.
* `AlgebraicGeometry.isLocallySurjective_of_isLocallySurjective_smallEtalePullback_module` and
  `AlgebraicGeometry.epi_of_epi_smallEtalePullback_module` — inverse image along a surjective
  morphism reflects local surjectivity, resp. epimorphisms, of sheaves of `Λ`-modules.

## References

* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 04FN](https://stacks.math.columbia.edu/tag/04FN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w uA vA u r

namespace AlgebraicGeometry

/-! ### Local surjectivity from surjectivity on the stalks, for arbitrary coefficients -/

section Coefficients

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A sieve through which every lift of every geometric point factors is a covering sieve: the
geometric point attached to a point of an étale neighbourhood lifts tautologically to it, so the
arrows of such a sieve are jointly surjective on points. -/
private theorem mem_topology_of_forall_lift {V : SmallEtale B S hS} (R : Sieve V)
    (hR : ∀ (s : GeometricPoint S) (q : (geometricPointFiber B S hS s).obj V),
      ∃ (W : SmallEtale B S hS) (g : W ⟶ V), R g ∧
        ∃ q' : (geometricPointFiber B S hS s).obj W,
          (geometricPointFiber B S hS s).map g q' = q) :
    R ∈ SmallEtale.topology B S hS V := by
  refine SmallEtale.mem_topology_of_jointlySurjective fun t => ?_
  obtain ⟨W, g, hg, q', hq'⟩ := hR (geometricPointOfEtalePoint B S hS V t)
    (geometricPointOfEtalePointLift B S hS V t)
  refine ⟨W, g, hg, q'.1.base default, ?_⟩
  have h1 : q'.1 ≫ (SmallEtale.toScheme B S hS).map g =
      (geometricPointOfEtalePointLift B S hS V t).1 := congrArg Subtype.val hq'
  have h2 : ((SmallEtale.toScheme B S hS).map g).base (q'.1.base default) =
      (geometricPointOfEtalePointLift B S hS V t).1.base default :=
    congrArg (fun m : (geometricPointOfEtalePoint B S hS V t).source ⟶ _ =>
      m.base (default : ↥(geometricPointOfEtalePoint B S hS V t).source)) h1
  exact h2.trans (geometricPointOfEtalePointLift_base B S hS V t)

variable (A : Type uA) [Category.{vA} A] {FC : A → A → Type*} {CC : A → Type w}
  [∀ P Q : A, FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{w} A FC]
  [HasColimitsOfSize.{u, u} A] [PreservesFilteredColimitsOfSize.{u, u} (forget A)]

/-- **Stacks 03PU** for an arbitrary concrete coefficient category. A map of sheaves on the small
étale site of `S` which is surjective on the stalk at every geometric point of `S` is locally
surjective.

A section over `V` is, near every point of `V`, the image of a section: its germ at the geometric
point attached to that point is the image of a germ, germs are computed on étale neighbourhoods,
and two sections with the same germ agree on an étale neighbourhood of the point. -/
@[stacks 03PU "local surjectivity from surjectivity on geometric stalks, arbitrary coefficients"]
public theorem isLocallySurjective_of_surjective_etaleStalkMapOfCoefficients
    {F G : Sheaf (SmallEtale.topology B S hS) A} (α : F ⟶ G)
    (h : ∀ s : GeometricPoint S, Function.Surjective
      ((etaleStalkPresheafFunctor B S hS s A).map α.hom)) :
    Presheaf.IsLocallySurjective (SmallEtale.topology B S hS) α.hom := by
  constructor
  intro V b
  refine mem_topology_of_forall_lift B S hS _ fun s q => ?_
  set Φ := geometricPointSitePoint B S hS s
  obtain ⟨z, hz⟩ := h s (Φ.toPresheafFiber V q G.obj b)
  obtain ⟨W, y, c, rfl⟩ := Φ.toPresheafFiber_jointly_surjective z
  replace hz : Φ.presheafFiber.map α.hom (Φ.toPresheafFiber W y F.obj c) =
      Φ.toPresheafFiber V q G.obj b := hz
  rw [Φ.toPresheafFiber_naturality_apply α.hom] at hz
  let ZW : Φ.fiber.Elements := Φ.fiber.elementsMk W y
  let ZV : Φ.fiber.Elements := Φ.fiber.elementsMk V q
  let Z : Φ.fiber.Elements := IsCofiltered.min ZW ZV
  let l : Z ⟶ ZW := IsCofiltered.minToLeft ZW ZV
  let r : Z ⟶ ZV := IsCofiltered.minToRight ZW ZV
  have hl : Φ.toPresheafFiber Z.obj Z.val G.obj (G.obj.map l.hom.op (α.hom.app (op W) c)) =
      Φ.toPresheafFiber W y G.obj (α.hom.app (op W) c) := by
    simpa only [ConcreteCategory.comp_apply, l.map_val] using
      ConcreteCategory.congr_hom (Φ.toPresheafFiber_w l.hom Z.val G.obj) (α.hom.app (op W) c)
  have hr : Φ.toPresheafFiber Z.obj Z.val G.obj (G.obj.map r.hom.op b) =
      Φ.toPresheafFiber V q G.obj b := by
    simpa only [ConcreteCategory.comp_apply, r.map_val] using
      ConcreteCategory.congr_hom (Φ.toPresheafFiber_w r.hom Z.val G.obj) b
  obtain ⟨Y, g, y', hy', heq⟩ :=
    (Φ.toPresheafFiber_eq_iff' Z.obj Z.val (G.obj.map l.hom.op (α.hom.app (op W) c))
      (G.obj.map r.hom.op b)).1 (hl.trans (hz.trans hr.symm))
  refine ⟨Y, g ≫ r.hom, ⟨F.obj.map (g ≫ l.hom).op c, ?_⟩, y', ?_⟩
  · rwa [NatTrans.naturality_apply, op_comp, op_comp, G.obj.map_comp, G.obj.map_comp,
      ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  · change Φ.fiber.map (g ≫ r.hom) y' = q
    rw [Functor.map_comp_apply, hy']
    exact r.map_val

end Coefficients

section NatIso

variable (A : Type uA) [Category.{vA} A] {FC : A → A → Type*} {CC : A → Type w}
  [∀ P Q : A, FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{w} A FC]

/-- Surjectivity of the map a functor to a concrete category induces on a morphism depends on the
functor only through its isomorphism class. -/
public lemma surjective_map_of_natIsoOfCoefficients {C : Type*} [Category* C] {L R : C ⥤ A}
    (e : L ≅ R) {P Q : C} (g : P ⟶ Q) (h : Function.Surjective (R.map g)) :
    Function.Surjective (L.map g) := by
  have hL : L.map g = e.hom.app P ≫ R.map g ≫ e.inv.app Q := by
    rw [← Category.assoc, ← e.hom.naturality g, Category.assoc, e.hom_inv_id_app,
      Category.comp_id]
  have hhom : Function.Surjective (e.hom.app P) :=
    (ConcreteCategory.bijective_of_isIso (e.hom.app P)).2
  have hinv : Function.Surjective (e.inv.app Q) :=
    (ConcreteCategory.bijective_of_isIso (e.inv.app Q)).2
  intro b
  obtain ⟨c, hc⟩ := hinv b
  obtain ⟨d, hd⟩ := h c
  obtain ⟨a, ha⟩ := hhom d
  refine ⟨a, ?_⟩
  rw [hL, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ha, hd, hc]

end NatIso

/-! ### Stalks of sheaves of modules -/

section Instances

variable (Λ : Type r) [CommRing Λ]

private instance hasLimitsOfShape_discrete_moduleCat (J : Type u) :
    HasLimitsOfShape (Discrete J) (ModuleCat.{max (u + 1) r} Λ) :=
  ModuleCat.hasLimitsOfShape

end Instances

section StalkFunctor

variable (B : BigEtaleSite.{u})

/-- The stalk at a geometric point, as a functor on the sheaves of `Λ`-modules of the small étale
site: a sheaf is restricted along the projection from the category of pointed étale
neighbourhoods and the colimit is taken there.

The ring universe `r` is free: the coefficient universe `max (u + 1) r` is the smallest one
containing both the site and the ring. -/
public abbrev etaleStalkFunctorModule (S : Scheme.{u}) (hS : B.Contains S)
    (Λ : Type r) [CommRing Λ] (s : GeometricPoint S) :
    Sheaf (SmallEtale.topology B S hS) (ModuleCat.{max (u + 1) r} Λ) ⥤
      ModuleCat.{max (u + 1) r} Λ :=
  sheafToPresheaf _ _ ⋙ etaleStalkPresheafFunctor B S hS s (ModuleCat.{max (u + 1) r} Λ)

end StalkFunctor

section Module

variable (B : BigEtaleSite.{u}) (Λ : Type (u + 1)) [CommRing Λ]

/-- **Stacks 03Q1 for sheaves of modules.** Inverse image of sheaves of `Λ`-modules on small
étale sites commutes with taking stalks at a geometric point: the stalk at `x` of the inverse
image along `f` is the stalk of the original sheaf at the image geometric point, naturally in the
sheaf. -/
@[stacks 03Q1 "module coefficients"]
public def smallEtalePullbackStalkIsoModule {S T : B.Scheme} (f : T ⟶ S)
    (x : GeometricPoint T.1) :
    (smallEtaleBaseChange B f).sheafPullback (ModuleCat.{u + 1} Λ)
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property) ⋙
      etaleStalkFunctorModule B T.1 T.property Λ x ≅
    etaleStalkFunctorModule B S.1 S.property Λ (x.map (B.inclusion.map f)) := by
  letI : HasProducts.{u} (ModuleCat.{u + 1} Λ) := fun _ => ModuleCat.hasLimitsOfShape
  exact smallEtalePullbackSheafFiberIso B f x (ModuleCat.{u + 1} Λ)

/-- **Stacks 03PU for sheaves of modules.** A locally surjective map of sheaves of `Λ`-modules on
a small étale site is surjective on the stalk at every geometric point: the stalk is the fiber of
the point of the site attached to the geometric point, and a point of a site turns local
surjectivity into surjectivity. -/
@[stacks 03PU "surjectivity on geometric stalks, module coefficients"]
public theorem surjective_etaleStalkMap_of_isLocallySurjective_module
    (S : Scheme.{u}) (hS : B.Contains S)
    {F G : Sheaf (SmallEtale.topology B S hS) (ModuleCat.{u + 1} Λ)} (α : F ⟶ G)
    [Presheaf.IsLocallySurjective (SmallEtale.topology B S hS) α.hom]
    (s : GeometricPoint S) :
    Function.Surjective
      ((etaleStalkPresheafFunctor B S hS s (ModuleCat.{u + 1} Λ)).map α.hom) :=
  (geometricPointSitePoint B S hS s).toPresheafFiber_map_surjective α.hom

/-- **Stacks 03PU for sheaves of modules.** A map of sheaves of `Λ`-modules on the small étale
site of `S` which is surjective on the stalk at every geometric point of `S` is locally
surjective. -/
@[stacks 03PU "local surjectivity from surjectivity on geometric stalks, module coefficients"]
public theorem isLocallySurjective_of_surjective_etaleStalkMap_module
    (S : Scheme.{u}) (hS : B.Contains S)
    {F G : Sheaf (SmallEtale.topology B S hS) (ModuleCat.{u + 1} Λ)} (α : F ⟶ G)
    (h : ∀ s : GeometricPoint S, Function.Surjective
      ((etaleStalkPresheafFunctor B S hS s (ModuleCat.{u + 1} Λ)).map α.hom)) :
    Presheaf.IsLocallySurjective (SmallEtale.topology B S hS) α.hom :=
  isLocallySurjective_of_surjective_etaleStalkMapOfCoefficients B S hS
    (ModuleCat.{u + 1} Λ) α h

end Module

/-! ### Descent of local surjectivity along a surjective morphism -/

section Descent

variable (B : BigEtaleSite.{u}) (Λ : Type (u + 1)) [CommRing Λ]

/-- **Local surjectivity of a map of sheaves of `Λ`-modules descends along a surjective
morphism.** If `α` induces a surjection on the stalk at `f ∘ x̄` for every geometric point `x̄` of
`X`, then `α` is locally surjective.

A geometric point of `Y` need not lift along a surjective `f`, but it has the same image point as
one of the form `f ∘ x̄`, and the stalk functors at two geometric points with the same image point
are isomorphic, naturally in the presheaf. -/
public theorem isLocallySurjective_of_surjective_pullback_etaleStalkMap_module
    {X Y : Scheme.{u}} (hY : B.Contains Y) (f : X ⟶ Y) (hf : Function.Surjective f.base)
    {F G : Sheaf (SmallEtale.topology B Y hY) (ModuleCat.{u + 1} Λ)} (α : F ⟶ G)
    (h : ∀ x : GeometricPoint X, Function.Surjective
      ((etaleStalkPresheafFunctor B Y hY (x.map f) (ModuleCat.{u + 1} Λ)).map α.hom)) :
    Presheaf.IsLocallySurjective (SmallEtale.topology B Y hY) α.hom :=
  isLocallySurjective_of_surjective_etaleStalkMap_module B Λ Y hY α fun s => by
    obtain ⟨x, hx⟩ := exists_geometricPoint_map_hom_base_eq_of_surjective f hf s
    exact surjective_map_of_natIsoOfCoefficients (ModuleCat.{u + 1} Λ)
      (etaleStalkPresheafFunctorIsoOfEqBase B Y hY hx (ModuleCat.{u + 1} Λ)).symm α.hom (h x)

variable {X Y : B.Scheme} (f : X ⟶ Y)

/-- Inverse image of sheaves of `Λ`-modules along a morphism of the big étale site, as a functor
between the categories of sheaves of modules on the small étale sites. -/
public abbrev smallEtaleModulePullbackFunctor :
    Sheaf (SmallEtale.topology B Y.1 Y.property) (ModuleCat.{u + 1} Λ) ⥤
      Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} Λ) :=
  (smallEtaleBaseChange B f).sheafPullback (ModuleCat.{u + 1} Λ)
    (SmallEtale.topology B Y.1 Y.property) (SmallEtale.topology B X.1 X.property)

/-- Surjectivity of `f⁻¹α` on the stalk at `x̄` gives surjectivity of `α` on the stalk at `f ∘ x̄`
(Stacks 03Q1). -/
private theorem surjective_etaleStalkMap_of_surjective_pullback_stalkMap
    {F G : Sheaf (SmallEtale.topology B Y.1 Y.property) (ModuleCat.{u + 1} Λ)} (α : F ⟶ G)
    (x : GeometricPoint X.1)
    (hX : Function.Surjective
      ((smallEtaleModulePullbackFunctor B Λ f ⋙
        etaleStalkFunctorModule B X.1 X.property Λ x).map α)) :
    Function.Surjective
      ((etaleStalkPresheafFunctor B Y.1 Y.property (x.map (B.inclusion.map f))
        (ModuleCat.{u + 1} Λ)).map α.hom) :=
  surjective_map_of_natIsoOfCoefficients (ModuleCat.{u + 1} Λ)
    (smallEtalePullbackStalkIsoModule B Λ f x).symm α hX

/-- **Inverse image along a surjective morphism reflects local surjectivity of maps of sheaves of
`Λ`-modules.** Let `f : X ⟶ Y` be surjective and `α` a map of sheaves of `Λ`-modules on
`Y_étale`. If `f⁻¹α` is locally surjective then so is `α`.

The stalk of `f⁻¹` at a geometric point `x̄` of `X` is the stalk at `f ∘ x̄` by Stacks 03Q1, so
local surjectivity of `f⁻¹α` gives surjectivity of `α` on the stalks at all the geometric points
of the form `f ∘ x̄`; those suffice because `f` is surjective. -/
public theorem isLocallySurjective_of_isLocallySurjective_smallEtalePullback_module
    (hf : Function.Surjective (B.inclusion.map f).base)
    {F G : Sheaf (SmallEtale.topology B Y.1 Y.property) (ModuleCat.{u + 1} Λ)} (α : F ⟶ G)
    (hα : Presheaf.IsLocallySurjective (SmallEtale.topology B X.1 X.property)
      ((smallEtaleModulePullbackFunctor B Λ f).map α).hom) :
    Presheaf.IsLocallySurjective (SmallEtale.topology B Y.1 Y.property) α.hom := by
  have := hα
  refine isLocallySurjective_of_surjective_pullback_etaleStalkMap_module B Λ Y.property
    (B.inclusion.map f) hf α fun x => ?_
  exact surjective_etaleStalkMap_of_surjective_pullback_stalkMap B Λ f α x
    (surjective_etaleStalkMap_of_isLocallySurjective_module B Λ X.1 X.property
      ((smallEtaleModulePullbackFunctor B Λ f).map α) x)

/-- **Inverse image along a surjective morphism reflects epimorphisms of sheaves of
`Λ`-modules.** For `f : X ⟶ Y` surjective, a map `α` of sheaves of `Λ`-modules on `Y_étale` with
`f⁻¹α` an epimorphism is itself an epimorphism. Together with the preservation of epimorphisms by
the left adjoint `f⁻¹`, this says that `f⁻¹` creates epimorphisms.

An epimorphism of sheaves is surjective on every stalk, because the stalk functor is a left
adjoint and an epimorphism of modules is a surjection; the stalks of `f⁻¹α` at the geometric
points of `X` are the stalks of `α` at the image points, and those detect local surjectivity,
which in turn gives an epimorphism. -/
public theorem epi_of_epi_smallEtalePullback_module
    (hf : Function.Surjective (B.inclusion.map f).base)
    {F G : Sheaf (SmallEtale.topology B Y.1 Y.property) (ModuleCat.{u + 1} Λ)} (α : F ⟶ G)
    (hα : Epi ((smallEtaleModulePullbackFunctor B Λ f).map α)) : Epi α := by
  have hstalk : ∀ x : GeometricPoint X.1, Function.Surjective
      ((etaleStalkPresheafFunctor B Y.1 Y.property (x.map (B.inclusion.map f))
        (ModuleCat.{u + 1} Λ)).map α.hom) := fun x => by
    have hepi : Epi ((etaleStalkFunctorModule B X.1 X.property Λ x).map
        ((smallEtaleModulePullbackFunctor B Λ f).map α)) := by
      have := hα
      change Epi ((geometricPointSitePoint B X.1 X.property x).sheafFiber.map
        ((smallEtaleModulePullbackFunctor B Λ f).map α))
      infer_instance
    exact surjective_etaleStalkMap_of_surjective_pullback_stalkMap B Λ f α x
      ((ModuleCat.epi_iff_surjective _).1 hepi)
  have := isLocallySurjective_of_surjective_pullback_etaleStalkMap_module B Λ Y.property
    (B.inclusion.map f) hf α hstalk
  infer_instance

end Descent

end AlgebraicGeometry

end
