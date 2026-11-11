module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Etale.SupportSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedImmersionsPushforward.AbelianSheafEssentialImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointDomination
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SupportedDerivedEquivalence

/-!
# Surjectivity of a map of étale sheaves descends along a surjective morphism

Let `f : X → Y` be a surjective morphism of schemes of a big étale site. A map of sheaves of
sets on `Y_étale` whose inverse image along `f` is locally surjective is itself locally
surjective, hence an epimorphism; so inverse image along a surjective morphism *reflects*
epimorphisms, and not merely preserves them.

Surjectivity of a map of étale sheaves is tested on the stalks at the geometric points
(Stacks 03PU), and the stalk of an inverse image at a geometric point `x̄` of `X` is the stalk
of the original sheaf at the image geometric point `f ∘ x̄` (Stacks 03Q1). What the argument
therefore needs is that the geometric points of the form `f ∘ x̄` already detect surjectivity
on `Y`, and this is where surjectivity of `f` enters.

A geometric point of `Y` does *not* in general lift along a surjective `f`: for `f` the
inclusion of the generic point `Spec k(t) → Spec k`, the geometric point `Spec k → Spec k` has
no lift, since `k(t)` admits no `k`-algebra map to `k`. What is true is that every geometric
point of `Y` has the *same image point* as one of the form `f ∘ x̄` — pick a point of `X` above
the image and take the algebraic closure of its residue field — and the étale stalk functor at
a geometric point depends only on the point of `Y` beneath it, by Stacks 04FN in the form
`AlgebraicGeometry.etaleStalkPresheafFunctorIsoOfEqBase`. Transporting surjectivity along that
isomorphism, which is natural in the presheaf, is the whole of the proof.

This is the step at which surjectivity of `f` is used in the proof of Stacks 095Q, that
constructibility of an étale sheaf on `Y` is detected by its inverse image along a surjective
morphism: a presentation of the sheaf as a filtered colimit of constructible ones becomes, after
inverse image, essentially constant, so one of the coprojections is an epimorphism after inverse
image, and the statement below carries that epimorphism back to `Y`. The remaining inputs of that
proof are Stacks 03SA and Stacks 095P; Stacks 095Q itself is stated and proved elsewhere, in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.SurjectiveDescent`,
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleSurjectiveDescent` and
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.AbelianSurjectiveDescent`.

## Main results

* `AlgebraicGeometry.exists_geometricPoint_map_hom_base_eq_of_surjective` — every geometric
  point of `Y` lies over the same point of `Y` as the image of some geometric point of `X`.
* `AlgebraicGeometry.surjective_etaleStalkPresheafFunctor_map_of_surjective` — surjectivity of
  the map induced on the stalks at the geometric points of the form `f ∘ x̄` implies
  surjectivity on the stalk at every geometric point of `Y`.
* `AlgebraicGeometry.isLocallySurjective_of_surjective_pullback_etaleStalkMap_type` — the same
  statement packaged as local surjectivity of a map of sheaves of sets on `Y_étale`.
* `AlgebraicGeometry.isLocallySurjective_of_isLocallySurjective_smallEtalePullback` and
  `AlgebraicGeometry.epi_of_epi_smallEtalePullback` — inverse image along a surjective morphism
  reflects local surjectivity, resp. epimorphisms, of sheaves of sets.

## References

* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 04FN](https://stacks.math.columbia.edu/tag/04FN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry

/-- Surjectivity of the map a set-valued functor induces on a morphism depends on the functor
only through its isomorphism class. -/
private theorem surjective_map_of_natIso {C : Type*} [Category* C]
    {L R : C ⥤ Type v} (e : L ≅ R) {A A' : C} (g : A ⟶ A')
    (h : Function.Surjective (R.map g)) : Function.Surjective (L.map g) := by
  have hL : L.map g = e.hom.app A ≫ R.map g ≫ e.inv.app A' := by
    rw [← Category.assoc, ← e.hom.naturality g, Category.assoc, e.hom_inv_id_app,
      Category.comp_id]
  have hhom : Function.Surjective (e.hom.app A) :=
    ((isIso_iff_bijective _).1 inferInstance).2
  have hinv : Function.Surjective (e.inv.app A') :=
    ((isIso_iff_bijective _).1 inferInstance).2
  rw [hL, types_comp, types_comp]
  exact (hinv.comp h).comp hhom

/-- For `f : X ⟶ Y` surjective, every geometric point of `Y` lies over the same point of `Y` as
the image under `f` of some geometric point of `X`: choose a point of `X` above the image of the
given geometric point and take the algebraic closure of its residue field.

The image geometric point itself need not be the given one — the two residue fields are
unrelated — which is why the conclusion is an equality of image points and not of geometric
points. -/
public theorem exists_geometricPoint_map_hom_base_eq_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : Function.Surjective f.base) (s : GeometricPoint Y) :
    ∃ x : GeometricPoint X, (x.map f).hom default = s.hom default := by
  obtain ⟨z, hz⟩ := hf (s.hom default)
  refine ⟨GeometricPoint.ofPoint X z, ?_⟩
  have h : (GeometricPoint.ofPoint X z).hom default = z := GeometricPoint.ofPoint_liesOver X z
  change f.base ((GeometricPoint.ofPoint X z).hom default) = s.hom default
  rw [h]
  exact hz

/-- **Surjectivity on étale stalks descends along a surjective morphism.** Let `f : X ⟶ Y` be a
surjective morphism of schemes and let `α` be a map of presheaves of sets on `Y_étale`. If the
map `α` induces on the stalk at `f ∘ x̄` is surjective for every geometric point `x̄` of `X`, then
the map it induces on the stalk at *every* geometric point of `Y` is surjective.

Every geometric point of `Y` has the same image point as one of the form `f ∘ x̄`, and the étale
stalk functors at two geometric points with the same image are isomorphic, naturally in the
presheaf; so the two induced maps differ by a bijection on each side. -/
public theorem surjective_etaleStalkPresheafFunctor_map_of_surjective (B : BigEtaleSite.{u})
    {X Y : Scheme.{u}} (hY : B.Contains Y) (f : X ⟶ Y) (hf : Function.Surjective f.base)
    {P Q : (SmallEtale B Y hY)ᵒᵖ ⥤ Type (u + 1)} (α : P ⟶ Q)
    (h : ∀ x : GeometricPoint X, Function.Surjective
      ((etaleStalkPresheafFunctor B Y hY (x.map f) (Type (u + 1))).map α))
    (s : GeometricPoint Y) :
    Function.Surjective ((etaleStalkPresheafFunctor B Y hY s (Type (u + 1))).map α) := by
  obtain ⟨x, hx⟩ := exists_geometricPoint_map_hom_base_eq_of_surjective f hf s
  exact surjective_map_of_natIso
    (etaleStalkPresheafFunctorIsoOfEqBase B Y hY hx (Type (u + 1))).symm α (h x)

/-- **Local surjectivity of a map of sheaves of sets on `Y_étale` descends along a surjective
morphism.** If `α` induces a surjection on the stalk at `f ∘ x̄` for every geometric point `x̄`
of `X`, then `α` is locally surjective.

This combines the previous lemma with Stacks 03PU on `Y`, in the form
`AlgebraicGeometry.isLocallySurjective_of_surjective_etaleStalkMap_type`. -/
public theorem isLocallySurjective_of_surjective_pullback_etaleStalkMap_type
    (B : BigEtaleSite.{u}) {X Y : Scheme.{u}} (hY : B.Contains Y) (f : X ⟶ Y)
    (hf : Function.Surjective f.base)
    {F G : Sheaf (SmallEtale.topology B Y hY) (Type (u + 1))} (α : F ⟶ G)
    (h : ∀ x : GeometricPoint X, Function.Surjective
      ((etaleStalkPresheafFunctor B Y hY (x.map f) (Type (u + 1))).map α.hom)) :
    Presheaf.IsLocallySurjective (SmallEtale.topology B Y hY) α.hom :=
  isLocallySurjective_of_surjective_etaleStalkMap_type B Y hY α fun s =>
    surjective_etaleStalkPresheafFunctor_map_of_surjective B hY f hf α.hom h s

section Pullback

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)

/-- Inverse image of sheaves of sets along a morphism of the big étale site, as a functor
between the small étale topoi, at the coefficient universe of the site. -/
public abbrev smallEtaleSetPullbackFunctor :
    Sheaf (SmallEtale.topology B Y.1 Y.property) (Type (u + 1)) ⥤
      Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1)) :=
  (smallEtaleBaseChange B f).sheafPullback (Type (u + 1))
    (SmallEtale.topology B Y.1 Y.property) (SmallEtale.topology B X.1 X.property)

/-- **Inverse image along a surjective morphism reflects local surjectivity of maps of sheaves
of sets.** Let `f : X ⟶ Y` be surjective and `α` a map of sheaves of sets on `Y_étale`. If
`f⁻¹α` is locally surjective then so is `α`.

The stalk of `f⁻¹` at a geometric point `x̄` of `X` is the stalk at `f ∘ x̄` by Stacks 03Q1, so
local surjectivity of `f⁻¹α` gives surjectivity of `α` on the stalks at all the geometric points
of the form `f ∘ x̄`; those suffice because `f` is surjective. -/
public theorem isLocallySurjective_of_isLocallySurjective_smallEtalePullback
    (hf : Function.Surjective (B.inclusion.map f).base)
    {F G : Sheaf (SmallEtale.topology B Y.1 Y.property) (Type (u + 1))} (α : F ⟶ G)
    (hα : Presheaf.IsLocallySurjective (SmallEtale.topology B X.1 X.property)
      ((smallEtaleSetPullbackFunctor B f).map α).hom) :
    Presheaf.IsLocallySurjective (SmallEtale.topology B Y.1 Y.property) α.hom := by
  have := hα
  refine isLocallySurjective_of_surjective_pullback_etaleStalkMap_type B Y.property
    (B.inclusion.map f) hf α fun x => ?_
  have hX : Function.Surjective
      ((smallEtaleSetPullbackFunctor B f ⋙
        etaleStalkFunctor.{u, u + 1} B X.1 X.property x).map α) :=
    (geometricPointSitePoint B X.1 X.property x).toPresheafFiber_map_surjective
      ((smallEtaleSetPullbackFunctor B f).map α).hom
  exact surjective_map_of_natIso (smallEtalePullbackStalkIso B f x).symm α hX

/-- **Inverse image along a surjective morphism reflects epimorphisms of sheaves of sets.** For
`f : X ⟶ Y` surjective, a map `α` of sheaves of sets on `Y_étale` with `f⁻¹α` an epimorphism is
itself an epimorphism. Together with the preservation of epimorphisms by the left adjoint `f⁻¹`,
this says that `f⁻¹` creates epimorphisms. -/
public theorem epi_of_epi_smallEtalePullback (hf : Function.Surjective (B.inclusion.map f).base)
    {F G : Sheaf (SmallEtale.topology B Y.1 Y.property) (Type (u + 1))} (α : F ⟶ G)
    (hα : Epi ((smallEtaleSetPullbackFunctor B f).map α)) : Epi α := by
  have h₁ : Presheaf.IsLocallySurjective (SmallEtale.topology B X.1 X.property)
      ((smallEtaleSetPullbackFunctor B f).map α).hom :=
    (Sheaf.isLocallySurjective_iff_epi ((smallEtaleSetPullbackFunctor B f).map α)).2 hα
  have := isLocallySurjective_of_isLocallySurjective_smallEtalePullback B f hf α h₁
  infer_instance

end Pullback

/-! ### Abelian coefficients -/

section Abelian

variable (B : BigEtaleSite.{u})

/-- **Local surjectivity of a map of abelian sheaves on `Y_étale` descends along a surjective
morphism.** If `α` induces a surjection on the stalk at `f ∘ x̄` for every geometric point `x̄` of
`X`, then `α` is locally surjective. The abelian form of
`AlgebraicGeometry.isLocallySurjective_of_surjective_pullback_etaleStalkMap_type`. -/
public theorem isLocallySurjective_of_surjective_pullback_etaleStalkMap_abelian
    {X Y : Scheme.{u}} (hY : B.Contains Y) (f : X ⟶ Y) (hf : Function.Surjective f.base)
    {F G : Sheaf (SmallEtale.topology B Y hY) AddCommGrpCat.{u + 1}} (α : F ⟶ G)
    (h : ∀ x : GeometricPoint X, Function.Surjective
      ((etaleStalkPresheafFunctor B Y hY (x.map f) AddCommGrpCat.{u + 1}).map α.hom)) :
    Presheaf.IsLocallySurjective (SmallEtale.topology B Y hY) α.hom :=
  isLocallySurjective_of_surjective_etaleStalkMap B Y hY α fun s => by
    obtain ⟨x, hx⟩ := exists_geometricPoint_map_hom_base_eq_of_surjective f hf s
    exact surjective_of_natIso
      (etaleStalkPresheafFunctorIsoOfEqBase B Y hY hx AddCommGrpCat.{u + 1}).symm α.hom (h x)

variable {X Y : B.Scheme} (f : X ⟶ Y)

/-- Inverse image of abelian sheaves along a morphism of the big étale site, as a functor
between the small étale topoi, at the coefficient universe of the site. -/
public abbrev smallEtaleAbelianPullbackFunctor :
    Sheaf (SmallEtale.topology B Y.1 Y.property) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1} :=
  (smallEtaleBaseChange B f).sheafPullback AddCommGrpCat.{u + 1}
    (SmallEtale.topology B Y.1 Y.property) (SmallEtale.topology B X.1 X.property)

/-- **Inverse image along a surjective morphism reflects local surjectivity of maps of abelian
sheaves.** Let `f : X ⟶ Y` be surjective and `α` a map of abelian sheaves on `Y_étale`. If
`f⁻¹α` is locally surjective then so is `α`. -/
public theorem isLocallySurjective_of_isLocallySurjective_smallEtalePullback_abelian
    (hf : Function.Surjective (B.inclusion.map f).base)
    {F G : Sheaf (SmallEtale.topology B Y.1 Y.property) AddCommGrpCat.{u + 1}} (α : F ⟶ G)
    (hα : Presheaf.IsLocallySurjective (SmallEtale.topology B X.1 X.property)
      ((smallEtaleAbelianPullbackFunctor B f).map α).hom) :
    Presheaf.IsLocallySurjective (SmallEtale.topology B Y.1 Y.property) α.hom := by
  have := hα
  refine isLocallySurjective_of_surjective_pullback_etaleStalkMap_abelian B Y.property
    (B.inclusion.map f) hf α fun x => ?_
  have hX : Function.Surjective
      ((smallEtaleAbelianPullbackFunctor B f ⋙
        etaleStalkFunctorAbelian B X.1 X.property x).map α) :=
    surjective_etaleStalkMap_of_isLocallySurjective B X.1 X.property
      ((smallEtaleAbelianPullbackFunctor B f).map α) x
  exact surjective_of_natIso (smallEtalePullbackStalkIsoAbelian B f x).symm α hX

end Abelian

end AlgebraicGeometry

end
