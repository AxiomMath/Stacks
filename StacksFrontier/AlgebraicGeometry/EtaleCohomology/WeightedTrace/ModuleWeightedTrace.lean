module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleProjectionIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceProperties
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The trace map of Stacks 0GKG built from the projection formula

Let `f : X ⟶ Y` be a locally quasi-finite morphism of a big étale site, let `Λ` be a commutative
ring and let `w : X → ℤ` be a weighting. [Stacks, Tag 0GKG] constructs the trace
`Tr_f : f_! f^{-1}G ⟶ G` for every sheaf `G` of `Λ`-modules on `Y_étale` out of the single trace
`Tr : f_!Λ ⟶ Λ` on the constant sheaf, by tensoring with `G` and transporting along the
projection formula [Stacks, Tag 0GKF]: the composite

`f_!(f^{-1}G) ≅ f_!Λ ⊗_Λ G --Tr ⊗ 1--> Λ ⊗_Λ G ≅ G`.

This file constructs that composite, with the trace on the constant sheaf — the unit `𝟙_` of the
monoidal structure on sheaves of `Λ`-modules — carried as a hypothesis, and proves that it has
the weighted trace stalks which characterise the trace, as soon as `Tr` has them.

## Main definitions

* `AlgebraicGeometry.SmallEtale.modShriekUnitTensorIso` — the projection formula at `F = 𝟙_`,
  `f_!(𝟙_) ⊗_Λ G ≅ f_!(f^{-1}G)`.
* `AlgebraicGeometry.SmallEtale.modWeightedTrace` — **the trace of [Stacks, Tag 0GKG]**:
  `f_!(f^{-1}G) ⟶ G`, built from a trace `Tr : f_!(𝟙_) ⟶ 𝟙_` on the constant sheaf.
* `AlgebraicGeometry.SmallEtale.modUnitWeightedSum` — the weighted sum over the geometric fibre
  on the constant sheaf, `⊕_{f(x̄) = ȳ} Λ ⟶ Λ`, with the summand indexed by `x̄` multiplied by
  the weight `w(x̄)`.
* `AlgebraicGeometry.SmallEtale.modWeightedTraceStalkMap` — the weighted sum over the geometric
  fibre for a general `G`, `⊕_{f(x̄) = ȳ} (f^{-1}G)_x̄ ⟶ G_ȳ`.
* `AlgebraicGeometry.SmallEtale.ModHasUnitTraceStalks` and
  `AlgebraicGeometry.SmallEtale.ModHasWeightedTraceStalks` — the characterising properties of
  the trace on the constant sheaf and of the trace on a general `G`: on every geometric stalk,
  read through the decomposition of the stalk of `f_!` over the geometric fibre, the map is the
  weighted sum.
* `AlgebraicGeometry.SmallEtale.modFiberStalkOf` and
  `AlgebraicGeometry.SmallEtale.modShriekFiberStalksIso` — the inclusion of the summand indexed
  by a point of the geometric fibre, and the stalk decomposition `(f_!F)_ȳ ≅ ⊕_{f(x̄) = ȳ} F_x̄`
  with that direct sum as its target.

## Main results

* `AlgebraicGeometry.SmallEtale.modHasWeightedTraceStalks_modWeightedTrace` — **[Stacks, Tag
  0GKG].** The trace built from the projection formula has the weighted trace stalks, as soon as
  the trace on the constant sheaf has them.
* `AlgebraicGeometry.SmallEtale.modStalkFunctor_map_modWeightedTrace` — **the stalk of the
  trace.** The stalk functor is monoidal, so on the stalk at `ȳ` the trace is the stalk of the
  projection formula followed by the stalk of `Tr`, read into `Λ`, acting on the left factor of
  `Λ ⊗_Λ G_ȳ`.
* `AlgebraicGeometry.SmallEtale.modStalkFunctor_μ_comp_modFShriekProjectionMap` — **the stalk of
  the comparison map of [Stacks, Tag 0GKF] is the stalk comparison of that tag**: through the
  decompositions of both stalks over the geometric fibre, it distributes the tensor product over
  the direct sum and compares summandwise.
* `AlgebraicGeometry.SmallEtale.presheafFiberModFiniteSupportStalkIso_eq` — **the germ
  decomposition of the fibre of `f_{p!}F` is the sheaf stalk decomposition of `f_!F`.** This is
  the `Λ`-linear form of
  `AlgebraicGeometry.SmallEtale.fShriekStalkIso_comp_sheafification`.
* `AlgebraicGeometry.SmallEtale.modStalkFunctor_μ` and
  `AlgebraicGeometry.SmallEtale.modProjectionFiberSummandIso_eq` — **the monoidality of the
  stalk functor on sheaves is the monoidality on presheaves**, composed with the fibre of the
  comparison of the pointwise tensor product with the tensor product of sheaves; hence the
  summand of the fibre comparison of the projection formula is the summand of the stalk
  comparison.
* `AlgebraicGeometry.SmallEtale.modFiberStalkOf_comp_modShriekStalkIso_naturality` — the stalk
  decomposition of `f_!` is natural on each summand of the geometric fibre.

## Implementation notes

The monoidal structure on sheaves of `Λ`-modules and the monoidality of the stalk functor are
not global instances; they are activated locally, and the local instance
`AlgebraicGeometry.SmallEtale.modStalkMonoidal` makes `CategoryTheory.Functor.Monoidal.εIso` of
the stalk functor available with the *same* instance as the one in
`AlgebraicGeometry.SmallEtale.modStalkTensorIso`.

**Two spellings of a stalk.** The fibre of a point of the site on *sheaves* is by definition the
fibre on *presheaves* of the underlying presheaf, and
`CategoryTheory.GrothendieckTopology.Point.presheafToSheafCompSheafFiberIso` is the inverse of
the fibre of `CategoryTheory.toSheafify`; so the two readings of a stalk differ by terms that
are definitionally equal but not syntactically so. A goal mixing them is not type-correct at the
`implicit` transparency level, where `rw` checks its motives, and every such rewrite fails with
`motive is not type correct` or a spurious `did not find the pattern`. The proofs below therefore
put each such crossing inside a `change`, a `congrArg` or an explicitly-typed `have`, and
`AlgebraicGeometry.SmallEtale.modShriekFiberStalksIso` exists only to name the composite whose
source and target are then spelled uniformly.

**No `stacks` attribute.** [Stacks, Tag 0GKG] also asserts that the trace exists — that is, that
the trace `Tr : f_!(𝟙_) ⟶ 𝟙_` on the constant sheaf exists and that the resulting `Tr_f` is the
unique map with these stalks. Only the construction from `Tr` and its stalk computation are
here, so the tag is not claimed.

## References

* [Stacks Project, Tag 0GKF](https://stacks.math.columbia.edu/tag/0GKF)
* [Stacks Project, Tag 0GKG](https://stacks.math.columbia.edu/tag/0GKG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped DirectSum

universe u v

namespace Stacks

/-- **The tensorator of a monoidal functor against the left unitor.** For a monoidal functor `F`
the comparison `F(𝟙_) ⊗ F(M) ⟶ F(𝟙_ ⊗ M)` followed by `F(λ_)` is the left unitor of `F(M)`,
after the unit comparison `𝟙_ ≅ F(𝟙_)` is undone. -/
public theorem laxMonoidal_μ_comp_map_leftUnitor {C : Type*} [Category* C] [MonoidalCategory C]
    {D : Type*} [Category* D] [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal] (M : C) :
    CategoryTheory.Functor.LaxMonoidal.μ F (𝟙_ C) M ≫ F.map (λ_ M).hom =
      (CategoryTheory.Functor.Monoidal.εIso F).inv ▷ F.obj M ≫ (λ_ (F.obj M)).hom := by
  rw [CategoryTheory.Functor.Monoidal.εIso_inv, CategoryTheory.Functor.Monoidal.map_leftUnitor,
    ← Category.assoc, CategoryTheory.Functor.Monoidal.μ_δ, Category.id_comp]

end Stacks

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (Λ : Type (max (u + 1) v)) [CommRing Λ] {X Y : B.Scheme}
  (f : X ⟶ Y)

attribute [local instance] moduleSheafMonoidal
attribute [local instance] SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat
attribute [local instance] hasLimitsOfSizeModuleCatSmall
attribute [local instance] preservesFilteredColimitsTensorLeftSmall
attribute [local instance] preservesFilteredColimitsTensorRightSmall
attribute [local instance] modStalkMonoidal

section SheafFiberMonoidal

variable (S : B.Scheme) (t : GeometricPoint S.obj)

/-- **The fibre of a sheafification is the fibre of the presheaf**: the comparison
`CategoryTheory.GrothendieckTopology.Point.presheafToSheafCompSheafFiberIso` at the point of the
small étale site attached to a geometric point, with coefficients in `Λ`-modules. -/
@[sga "4 VIII 3.9" "partial"]
public abbrev modSheafifyStalkIso :
    presheafToSheaf (SmallEtale.topology B S.obj S.property) (ModuleCat.{max (u + 1) v} Λ) ⋙
        modStalkFunctor.{u, v, max (u + 1) v} B Λ S t ≅
      (geometricPointSitePoint B S.obj S.property t).presheafFiber :=
  (geometricPointSitePoint B S.obj S.property t).presheafToSheafCompSheafFiberIso
    (ModuleCat.{max (u + 1) v} Λ)

/-- **The comparison of the fibre of a sheafification with the fibre of the presheaf is, read
backwards, the fibre of the sheafification unit.** -/
public theorem modSheafifyStalkIso_inv_app
    (P : (SmallEtale B S.obj S.property)ᵒᵖ ⥤ ModuleCat.{max (u + 1) v} Λ) :
    (modSheafifyStalkIso.{u, v} B Λ S t).inv.app P =
      (geometricPointSitePoint B S.obj S.property t).presheafFiber.map
        (toSheafify (SmallEtale.topology B S.obj S.property) P) :=
  rfl

/-- **The fibre of the counit of sheafification at a sheaf** is the comparison of the fibre of
the sheafification with the fibre of the presheaf. -/
public theorem modStalkFunctor_map_sheafificationAdjunction_counit
    (F : ModuleSheaf.{u, v, max (u + 1) v} B S Λ) :
    (modStalkFunctor.{u, v, max (u + 1) v} B Λ S t).map
        ((sheafificationAdjunction (SmallEtale.topology B S.obj S.property)
          (ModuleCat.{max (u + 1) v} Λ)).counit.app F) =
      (modSheafifyStalkIso.{u, v} B Λ S t).hom.app F.obj := by
  have h : (modSheafifyStalkIso.{u, v} B Λ S t).inv.app F.obj ≫
        (modStalkFunctor.{u, v, max (u + 1) v} B Λ S t).map
          ((sheafificationAdjunction (SmallEtale.topology B S.obj S.property)
            (ModuleCat.{max (u + 1) v} Λ)).counit.app F) = 𝟙 _ := by
    rw [modSheafifyStalkIso_inv_app]
    change (geometricPointSitePoint B S.obj S.property t).presheafFiber.map
          (toSheafify (SmallEtale.topology B S.obj S.property) F.obj) ≫
        (geometricPointSitePoint B S.obj S.property t).presheafFiber.map
          (((sheafificationAdjunction (SmallEtale.topology B S.obj S.property)
            (ModuleCat.{max (u + 1) v} Λ)).counit.app F).hom) = 𝟙 _
    rw [← Functor.map_comp]
    simp
  exact (cancel_epi ((modSheafifyStalkIso.{u, v} B Λ S t).inv.app F.obj)).1
    (h.trans ((modSheafifyStalkIso.{u, v} B Λ S t).inv_hom_id_app F.obj).symm)

/-- **The fibre of the comparison of the pointwise tensor product with the tensor product of
sheaves of `Λ`-modules**, in terms of the fibre of the sheafification unit and the monoidality
of sheafification. -/
public theorem presheafFiber_map_moduleToTensorSection
    (F G : ModuleSheaf.{u, v, max (u + 1) v} B S Λ) :
    (geometricPointSitePoint B S.obj S.property t).presheafFiber.map
        (Stacks.ModuleSheafTensorSection.moduleToTensorSection
          (SmallEtale.topology B S.obj S.property) Λ F G) =
      (modSheafifyStalkIso.{u, v} B Λ S t).inv.app (F.obj ⊗ G.obj) ≫
        (modStalkFunctor.{u, v, max (u + 1) v} B Λ S t).map
          ((Functor.Monoidal.μIso (presheafToSheaf (SmallEtale.topology B S.obj S.property)
              (ModuleCat.{max (u + 1) v} Λ)) F.obj G.obj).inv ≫
            ((sheafificationAdjunction (SmallEtale.topology B S.obj S.property)
                (ModuleCat.{max (u + 1) v} Λ)).counit.app F ⊗ₘ
              (sheafificationAdjunction (SmallEtale.topology B S.obj S.property)
                (ModuleCat.{max (u + 1) v} Λ)).counit.app G)) := by
  rw [modSheafifyStalkIso_inv_app]
  change _ = (geometricPointSitePoint B S.obj S.property t).presheafFiber.map
        (toSheafify (SmallEtale.topology B S.obj S.property) (F.obj ⊗ G.obj)) ≫
      (geometricPointSitePoint B S.obj S.property t).presheafFiber.map
        ((sheafToPresheaf (SmallEtale.topology B S.obj S.property)
            (ModuleCat.{max (u + 1) v} Λ)).map
          ((Functor.Monoidal.μIso (presheafToSheaf (SmallEtale.topology B S.obj S.property)
              (ModuleCat.{max (u + 1) v} Λ)) F.obj G.obj).inv ≫
            ((sheafificationAdjunction (SmallEtale.topology B S.obj S.property)
                (ModuleCat.{max (u + 1) v} Λ)).counit.app F ⊗ₘ
              (sheafificationAdjunction (SmallEtale.topology B S.obj S.property)
                (ModuleCat.{max (u + 1) v} Λ)).counit.app G)))
  rw [← Functor.map_comp]
  rfl

/-- **The tensorator of the stalk functor on sheaves of `Λ`-modules is the tensorator on
presheaves**, followed by the fibre of the comparison of the pointwise tensor product with the
tensor product of sheaves. -/
public theorem modStalkFunctor_μ (F G : ModuleSheaf.{u, v, max (u + 1) v} B S Λ) :
    Functor.LaxMonoidal.μ (modStalkFunctor.{u, v, max (u + 1) v} B Λ S t) F G =
      Functor.LaxMonoidal.μ
          ((geometricPointSitePoint B S.obj S.property t).presheafFiber) F.obj G.obj ≫
        (geometricPointSitePoint B S.obj S.property t).presheafFiber.map
          (Stacks.ModuleSheafTensorSection.moduleToTensorSection
            (SmallEtale.topology B S.obj S.property) Λ F G) := by
  have hmon := NatTrans.IsMonoidal.tensor
    (τ := (modSheafifyStalkIso.{u, v} B Λ S t).hom) F.obj G.obj
  rw [Functor.LaxMonoidal.comp_μ] at hmon
  have hnat := Functor.LaxMonoidal.μ_natural
    (modStalkFunctor.{u, v, max (u + 1) v} B Λ S t)
    ((sheafificationAdjunction (SmallEtale.topology B S.obj S.property)
      (ModuleCat.{max (u + 1) v} Λ)).counit.app F)
    ((sheafificationAdjunction (SmallEtale.topology B S.obj S.property)
      (ModuleCat.{max (u + 1) v} Λ)).counit.app G)
  rw [modStalkFunctor_map_sheafificationAdjunction_counit,
    modStalkFunctor_map_sheafificationAdjunction_counit] at hnat
  simp only [CategoryTheory.Functor.id_obj] at hnat
  have hμ : Functor.LaxMonoidal.μ (presheafToSheaf (SmallEtale.topology B S.obj S.property)
          (ModuleCat.{max (u + 1) v} Λ)) F.obj G.obj ≫
      (Functor.Monoidal.μIso (presheafToSheaf (SmallEtale.topology B S.obj S.property)
        (ModuleCat.{max (u + 1) v} Λ)) F.obj G.obj).inv = 𝟙 _ := by
    rw [Functor.Monoidal.μIso_inv]
    exact Functor.Monoidal.μ_δ _ _ _
  have hcore : Functor.LaxMonoidal.μ (modStalkFunctor.{u, v, max (u + 1) v} B Λ S t)
          ((presheafToSheaf (SmallEtale.topology B S.obj S.property)
            (ModuleCat.{max (u + 1) v} Λ)).obj F.obj)
          ((presheafToSheaf (SmallEtale.topology B S.obj S.property)
            (ModuleCat.{max (u + 1) v} Λ)).obj G.obj) ≫
        (modStalkFunctor.{u, v, max (u + 1) v} B Λ S t).map
          ((sheafificationAdjunction (SmallEtale.topology B S.obj S.property)
              (ModuleCat.{max (u + 1) v} Λ)).counit.app F ⊗ₘ
            (sheafificationAdjunction (SmallEtale.topology B S.obj S.property)
              (ModuleCat.{max (u + 1) v} Λ)).counit.app G) =
      ((modSheafifyStalkIso.{u, v} B Λ S t).hom.app F.obj ⊗ₘ
          (modSheafifyStalkIso.{u, v} B Λ S t).hom.app G.obj) ≫
        Functor.LaxMonoidal.μ
            ((geometricPointSitePoint B S.obj S.property t).presheafFiber) F.obj G.obj ≫
          (modSheafifyStalkIso.{u, v} B Λ S t).inv.app (F.obj ⊗ G.obj) ≫
            (modStalkFunctor.{u, v, max (u + 1) v} B Λ S t).map
              ((Functor.Monoidal.μIso (presheafToSheaf
                  (SmallEtale.topology B S.obj S.property)
                  (ModuleCat.{max (u + 1) v} Λ)) F.obj G.obj).inv ≫
                ((sheafificationAdjunction (SmallEtale.topology B S.obj S.property)
                    (ModuleCat.{max (u + 1) v} Λ)).counit.app F ⊗ₘ
                  (sheafificationAdjunction (SmallEtale.topology B S.obj S.property)
                    (ModuleCat.{max (u + 1) v} Λ)).counit.app G)) := by
    rw [← Category.assoc, ← hmon, Category.assoc, Category.assoc,
      Iso.hom_inv_id_app_assoc, ← Functor.map_comp, ← Category.assoc, hμ, Category.id_comp]
  refine (cancel_epi ((modSheafifyStalkIso.{u, v} B Λ S t).hom.app F.obj ⊗ₘ
    (modSheafifyStalkIso.{u, v} B Λ S t).hom.app G.obj)).1 ?_
  rw [presheafFiber_map_moduleToTensorSection]
  exact hnat.trans hcore

/-- **The comparison of the sheaf fibre with the fibre of the underlying abelian sheaf is the
presheaf comparison at the underlying presheaf.** -/
public theorem sheafFiberCompIso_hom_app_eq (M : ModuleSheaf.{u, v, max (u + 1) v} B S Λ) :
    ((geometricPointSitePoint B S.obj S.property t).sheafFiberCompIso
          (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v})).hom.app M =
      ((geometricPointSitePoint B S.obj S.property t).presheafFiberCompIso
        (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v})).hom.app M.obj := by
  change ((geometricPointSitePoint B S.obj S.property t).presheafFiberCompIso
      (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v})).hom.app M.obj ≫
    𝟙 _ = _
  exact Category.comp_id _

/-- The presheaf comparison at the presheaf underlying a sheaf cancels the sheaf comparison. -/
public theorem presheafFiberCompIso_hom_app_sheafFiberCompIso_inv_app
    (M : ModuleSheaf.{u, v, max (u + 1) v} B S Λ) :
    ((geometricPointSitePoint B S.obj S.property t).presheafFiberCompIso
          (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v})).hom.app M.obj ≫
        ((geometricPointSitePoint B S.obj S.property t).sheafFiberCompIso
          (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v})).inv.app M =
      𝟙 _ := by
  rw [← sheafFiberCompIso_hom_app_eq]
  exact Iso.hom_inv_id_app _ _

/-- **The underlying map of abelian groups of the comparison of the two `Λ`-module structures on
a stalk**, read backwards. -/
public theorem forget₂_map_moduleEtaleStalkIso_inv_app
    (M : ModuleSheaf.{u, v, max (u + 1) v} B S Λ) :
    (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}).map
        ((moduleEtaleStalkIso.{u, v, max (u + 1) v} B Λ S t).inv.app M) =
      ((geometricPointSitePoint B S.obj S.property t).sheafFiberCompIso
        (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v})).inv.app M := by
  have h1 : (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}).map
        ((moduleEtaleStalkIso.{u, v, max (u + 1) v} B Λ S t).hom.app M) =
      ((geometricPointSitePoint B S.obj S.property t).sheafFiberCompIso
        (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v})).hom.app M := rfl
  have h2 : (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}).map
        ((moduleEtaleStalkIso.{u, v, max (u + 1) v} B Λ S t).inv.app M) ≫
      ((geometricPointSitePoint B S.obj S.property t).sheafFiberCompIso
        (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v})).hom.app M =
      𝟙 _ := by
    rw [← h1, ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  refine (cancel_mono (((geometricPointSitePoint B S.obj S.property t).sheafFiberCompIso
    (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v})).hom.app M)).1 ?_
  exact h2.trans (Iso.inv_hom_id_app
    ((geometricPointSitePoint B S.obj S.property t).sheafFiberCompIso
      (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v})) M).symm

/-- **The fibre of a morphism of presheaves of `Λ`-modules, on underlying abelian groups.** -/
public theorem forget₂_map_presheafFiber_map
    {P Q : (SmallEtale B S.obj S.property)ᵒᵖ ⥤ ModuleCat.{max (u + 1) v} Λ} (g : P ⟶ Q) :
    (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}).map
        ((geometricPointSitePoint B S.obj S.property t).presheafFiber.map g) =
      ((geometricPointSitePoint B S.obj S.property t).presheafFiberCompIso
            (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v})).inv.app P ≫
        (geometricPointSitePoint B S.obj S.property t).presheafFiber.map
            (Functor.whiskerRight g
              (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v})) ≫
          ((geometricPointSitePoint B S.obj S.property t).presheafFiberCompIso
            (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v})).hom.app Q := by
  have hnat := ((geometricPointSitePoint B S.obj S.property t).presheafFiberCompIso
    (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v})).hom.naturality g
  simp only [CategoryTheory.Functor.comp_map, Functor.whiskeringRight_obj_map] at hnat
  rw [hnat, Iso.inv_hom_id_app_assoc]

/-- **The fibre of a morphism of sheaves of `Λ`-modules, on underlying abelian groups**, read
against the comparison of the fibre with the fibre of the underlying abelian sheaf. -/
public theorem forget₂_map_modStalkFunctor_map_comp_sheafFiberCompIso_inv_app
    {M N : ModuleSheaf.{u, v, max (u + 1) v} B S Λ} (h : M ⟶ N) :
    (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}).map
          ((modStalkFunctor.{u, v, max (u + 1) v} B Λ S t).map h) ≫
        ((geometricPointSitePoint B S.obj S.property t).sheafFiberCompIso
          (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v})).inv.app N =
      ((geometricPointSitePoint B S.obj S.property t).sheafFiberCompIso
            (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v})).inv.app M ≫
        (geometricPointSitePoint B S.obj S.property t).presheafFiber.map
          (Functor.whiskerRight h.hom
            (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v})) := by
  have hnat := ((geometricPointSitePoint B S.obj S.property t).sheafFiberCompIso
    (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v})).inv.naturality h
  simp only [CategoryTheory.Functor.comp_map] at hnat
  exact hnat

/-- The reassociated form of
`AlgebraicGeometry.SmallEtale.presheafFiberCompIso_hom_app_sheafFiberCompIso_inv_app`. -/
public theorem presheafFiberCompIso_hom_app_sheafFiberCompIso_inv_app_assoc
    (M : ModuleSheaf.{u, v, max (u + 1) v} B S Λ) {Z : AddCommGrpCat.{max (u + 1) v}}
    (g : (geometricPointSitePoint B S.obj S.property t).sheafFiber.obj
        ((forgetModuleSheaf.{u, v, max (u + 1) v} B S Λ).obj M) ⟶ Z) :
    ((geometricPointSitePoint B S.obj S.property t).presheafFiberCompIso
          (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v})).hom.app M.obj ≫
        ((geometricPointSitePoint B S.obj S.property t).sheafFiberCompIso
          (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v})).inv.app M ≫ g =
      g :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun m => m ≫ g)
      (presheafFiberCompIso_hom_app_sheafFiberCompIso_inv_app B Λ S t M)).trans
      (Category.id_comp g))

/-- **The fibre of the sheafification of a morphism of presheaves of `Λ`-modules** is the fibre
of the morphism, read through the comparison of the fibre of a sheafification with the fibre of
the presheaf. -/
public theorem modStalkFunctor_map_presheafToSheaf_map
    {P Q : (SmallEtale B S.obj S.property)ᵒᵖ ⥤ ModuleCat.{max (u + 1) v} Λ} (g : P ⟶ Q) :
    (modStalkFunctor.{u, v, max (u + 1) v} B Λ S t).map
        ((presheafToSheaf (SmallEtale.topology B S.obj S.property)
          (ModuleCat.{max (u + 1) v} Λ)).map g) =
      (modSheafifyStalkIso.{u, v} B Λ S t).hom.app P ≫
        (geometricPointSitePoint B S.obj S.property t).presheafFiber.map g ≫
          (modSheafifyStalkIso.{u, v} B Λ S t).inv.app Q := by
  have hnat := (modSheafifyStalkIso.{u, v} B Λ S t).hom.naturality g
  simp only [CategoryTheory.Functor.comp_map] at hnat
  rw [← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

/-- **The fibre of the inverse of the counit of sheafification** cancels the comparison of the
fibre of a sheafification with the fibre of the presheaf. -/
public theorem modStalkFunctor_map_counit_symm_hom_comp
    (M : ModuleSheaf.{u, v, max (u + 1) v} B S Λ) :
    (modStalkFunctor.{u, v, max (u + 1) v} B Λ S t).map
          ((asIso ((sheafificationAdjunction (SmallEtale.topology B S.obj S.property)
            (ModuleCat.{max (u + 1) v} Λ)).counit.app M)).symm.hom) ≫
        (modSheafifyStalkIso.{u, v} B Λ S t).hom.app M.obj = 𝟙 _ := by
  change (modStalkFunctor.{u, v, max (u + 1) v} B Λ S t).map
        (inv ((sheafificationAdjunction (SmallEtale.topology B S.obj S.property)
          (ModuleCat.{max (u + 1) v} Λ)).counit.app M)) ≫
      (modSheafifyStalkIso.{u, v} B Λ S t).hom.app M.obj = 𝟙 _
  have h1 : (modStalkFunctor.{u, v, max (u + 1) v} B Λ S t).map
        (inv ((sheafificationAdjunction (SmallEtale.topology B S.obj S.property)
          (ModuleCat.{max (u + 1) v} Λ)).counit.app M)) ≫
      (modStalkFunctor.{u, v, max (u + 1) v} B Λ S t).map
        ((sheafificationAdjunction (SmallEtale.topology B S.obj S.property)
          (ModuleCat.{max (u + 1) v} Λ)).counit.app M) = 𝟙 _ := by
    rw [← Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id]
  exact (congrArg (fun m => (modStalkFunctor.{u, v, max (u + 1) v} B Λ S t).map
      (inv ((sheafificationAdjunction (SmallEtale.topology B S.obj S.property)
        (ModuleCat.{max (u + 1) v} Λ)).counit.app M)) ≫ m)
    (modStalkFunctor_map_sheafificationAdjunction_counit B Λ S t M).symm).trans h1

end SheafFiberMonoidal

variable [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]

/-- **The stalk decomposition of the direct image with compact support**, with the direct sum
over the geometric fibre in the form `AlgebraicGeometry.SmallEtale.modFiberStalks`:
`(f_!F)_ȳ ≅ ⊕_{f(x̄) = ȳ} F_x̄`. -/
public def modShriekFiberStalksIso (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ) :
    (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj
        ((fShriekMod.{u, v, max (u + 1) v} B Λ f).obj F) ≅
      modFiberStalks.{u, v, max (u + 1) v} B Λ f s F :=
  (modShriekStalkIso.{u, v, max (u + 1) v} B Λ f s).app F ≪≫
    moduleFiberStalksIso.{u, v, max (u + 1) v} B Λ f s F

section FiniteSupportFiberComparison

/-- **The underlying map of abelian groups of the `Λ`-linear stalk decomposition of `f_!`.** -/
public theorem forget₂_map_modShriekStalkIso_app_hom (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ) :
    (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}).map
        ((modShriekStalkIso.{u, v, max (u + 1) v} B Λ f s).app F).hom =
      ((geometricPointSitePoint B Y.obj Y.property s).sheafFiberCompIso
            (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v})).inv.app
          ((fShriekMod.{u, v, max (u + 1) v} B Λ f).obj F) ≫
        (fShriekStalkIso B f s
          ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F)).hom := by
  change (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}).map
      ((moduleEtaleStalkIso.{u, v, max (u + 1) v} B Λ Y s).inv.app
          ((fShriekMod.{u, v, max (u + 1) v} B Λ f).obj F) ≫
        (moduleFShriekStalkIso.{u, v, max (u + 1) v} B Λ f s F).hom) = _
  rw [Functor.map_comp, forget₂_map_moduleEtaleStalkIso_inv_app, moduleFShriekStalkIso_forget₂]
  rfl

/-- **Sheafification of the finite-support direct image commutes with forgetting the module
structure, on the sheafification unit.** The underlying morphism of abelian presheaves of
`AlgebraicGeometry.SmallEtale.fShriekModSheafifyIso` carries the abelian sheafification unit of
`f_{p!}F` to the sheafification unit of the presheaf of `Λ`-modules. -/
public theorem toSheafify_comp_whiskerRight_fShriekModSheafifyIso_hom
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ) :
    toSheafify (SmallEtale.topology B Y.obj Y.property)
          ((finiteSupportPushforward.{u, max (u + 1) v} B f (fun _ => inferInstance)).1.obj
            ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F)) ≫
        Functor.whiskerRight (fShriekModSheafifyIso.{u, v, max (u + 1) v} B Λ f F).hom.hom
          (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}) =
      Functor.whiskerRight (toSheafify (SmallEtale.topology B Y.obj Y.property)
          ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F))
        (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}) := by
  let := preservesSheafification_forgetModuleCat.{u, v, max (u + 1) v} B Y Λ
  exact sheafComposeIso_hom_fac (SmallEtale.topology B Y.obj Y.property)
    (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v})
    ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F)

/-- The abelian sheafification unit of `f_{p!}F`, read through
`AlgebraicGeometry.SmallEtale.fShriekModSheafifyIso` backwards. -/
public theorem whiskerRight_toSheafify_comp_whiskerRight_fShriekModSheafifyIso_inv
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ) :
    Functor.whiskerRight (toSheafify (SmallEtale.topology B Y.obj Y.property)
            ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F))
          (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}) ≫
        Functor.whiskerRight (fShriekModSheafifyIso.{u, v, max (u + 1) v} B Λ f F).inv.hom
          (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}) =
      toSheafify (SmallEtale.topology B Y.obj Y.property)
        ((finiteSupportPushforward.{u, max (u + 1) v} B f (fun _ => inferInstance)).1.obj
          ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F)) := by
  have hid : Functor.whiskerRight (fShriekModSheafifyIso.{u, v, max (u + 1) v} B Λ f F).hom.hom
        (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}) ≫
      Functor.whiskerRight (fShriekModSheafifyIso.{u, v, max (u + 1) v} B Λ f F).inv.hom
        (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}) = 𝟙 _ := by
    rw [← Functor.whiskerRight_comp]
    change Functor.whiskerRight
        ((fShriekModSheafifyIso.{u, v, max (u + 1) v} B Λ f F).hom ≫
          (fShriekModSheafifyIso.{u, v, max (u + 1) v} B Λ f F).inv).hom
        (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}) = _
    rw [Iso.hom_inv_id]
    simp
  refine (congrArg (fun m => m ≫ Functor.whiskerRight
        (fShriekModSheafifyIso.{u, v, max (u + 1) v} B Λ f F).inv.hom
        (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}))
      (toSheafify_comp_whiskerRight_fShriekModSheafifyIso_hom B Λ f F).symm).trans ?_
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun m => toSheafify (SmallEtale.topology B Y.obj Y.property)
        ((finiteSupportPushforward.{u, max (u + 1) v} B f (fun _ => inferInstance)).1.obj
          ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F)) ≫ m) hid).trans
      (Category.comp_id _))

/-- **The two readings of the fibre of the finite-support direct image agree.** The germ
decomposition `AlgebraicGeometry.SmallEtale.modFiniteSupportFiberIso` of the fibre of `f_{p!}F` is
the decomposition `AlgebraicGeometry.SmallEtale.presheafFiberModFiniteSupportStalkIso` obtained
from the *sheaf* decomposition `AlgebraicGeometry.SmallEtale.modShriekStalkIso` of the stalk of
`f_!F`. This is the `Λ`-linear form of
`AlgebraicGeometry.SmallEtale.fShriekStalkIso_comp_sheafification`. -/
public theorem presheafFiberModFiniteSupportStalkIso_eq (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ) :
    presheafFiberModFiniteSupportStalkIso.{u, v} B Λ f F s =
      modFiniteSupportFiberIso.{u, v} B Λ f F s := by
  have key : (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}).map
          ((geometricPointSitePoint B Y.obj Y.property s).presheafFiber.map
            (toSheafify (SmallEtale.topology B Y.obj Y.property)
              ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F))) ≫
        (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}).map
            ((modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).map
              (fShriekModSheafifyIso.{u, v, max (u + 1) v} B Λ f F).inv) ≫
          ((geometricPointSitePoint B Y.obj Y.property s).sheafFiberCompIso
            (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v})).inv.app
              ((fShriekMod.{u, v, max (u + 1) v} B Λ f).obj F) =
      ((geometricPointSitePoint B Y.obj Y.property s).presheafFiberCompIso
            (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v})).inv.app
          ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F) ≫
        (geometricPointSitePoint B Y.obj Y.property s).presheafFiber.map
          (toSheafify (SmallEtale.topology B Y.obj Y.property)
            ((finiteSupportPushforward.{u, max (u + 1) v} B f (fun _ => inferInstance)).1.obj
              ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F))) := by
    have hA := forget₂_map_presheafFiber_map B Λ Y s
      (toSheafify (SmallEtale.topology B Y.obj Y.property)
        ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F))
    have hB := forget₂_map_modStalkFunctor_map_comp_sheafFiberCompIso_inv_app B Λ Y s
      (fShriekModSheafifyIso.{u, v, max (u + 1) v} B Λ f F).inv
    have hC := presheafFiberCompIso_hom_app_sheafFiberCompIso_inv_app_assoc B Λ Y s
      ((presheafToSheaf (SmallEtale.topology B Y.obj Y.property)
          (ModuleCat.{max (u + 1) v} Λ)).obj
        ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F))
      ((geometricPointSitePoint B Y.obj Y.property s).presheafFiber.map
        (Functor.whiskerRight (fShriekModSheafifyIso.{u, v, max (u + 1) v} B Λ f F).inv.hom
          (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v})))
    have hWV := ((geometricPointSitePoint B Y.obj Y.property s).presheafFiber.map_comp
          (Functor.whiskerRight (toSheafify (SmallEtale.topology B Y.obj Y.property)
              ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F))
            (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}))
          (Functor.whiskerRight (fShriekModSheafifyIso.{u, v, max (u + 1) v} B Λ f F).inv.hom
            (forget₂ (ModuleCat.{max (u + 1) v} Λ)
              AddCommGrpCat.{max (u + 1) v}))).symm.trans
      (congrArg (geometricPointSitePoint B Y.obj Y.property s).presheafFiber.map
        (whiskerRight_toSheafify_comp_whiskerRight_fShriekModSheafifyIso_inv B Λ f F))
    refine (congrArg (fun m =>
      (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}).map
          ((geometricPointSitePoint B Y.obj Y.property s).presheafFiber.map
            (toSheafify (SmallEtale.topology B Y.obj Y.property)
              ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F))) ≫ m) hB).trans ?_
    refine (congrArg (fun m => m ≫
      (((geometricPointSitePoint B Y.obj Y.property s).sheafFiberCompIso
            (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v})).inv.app
          ((presheafToSheaf (SmallEtale.topology B Y.obj Y.property)
              (ModuleCat.{max (u + 1) v} Λ)).obj
            ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F)) ≫
        (geometricPointSitePoint B Y.obj Y.property s).presheafFiber.map
          (Functor.whiskerRight (fShriekModSheafifyIso.{u, v, max (u + 1) v} B Λ f F).inv.hom
            (forget₂ (ModuleCat.{max (u + 1) v} Λ)
              AddCommGrpCat.{max (u + 1) v})))) hA).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun m =>
      ((geometricPointSitePoint B Y.obj Y.property s).presheafFiberCompIso
            (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v})).inv.app
          ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F) ≫ m)
      (Category.assoc _ _ _)).trans ?_
    exact (congrArg (fun m =>
      ((geometricPointSitePoint B Y.obj Y.property s).presheafFiberCompIso
            (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v})).inv.app
          ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F) ≫
        (geometricPointSitePoint B Y.obj Y.property s).presheafFiber.map
            (Functor.whiskerRight (toSheafify (SmallEtale.topology B Y.obj Y.property)
                ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F))
              (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v})) ≫ m)
      hC).trans
      (congrArg (fun m =>
        ((geometricPointSitePoint B Y.obj Y.property s).presheafFiberCompIso
              (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v})).inv.app
            ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F) ≫ m) hWV)
  refine Iso.ext ((forget₂ (ModuleCat.{max (u + 1) v} Λ)
    AddCommGrpCat.{max (u + 1) v}).map_injective ?_)
  change (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}).map
        ((geometricPointSitePoint B Y.obj Y.property s).presheafFiber.map
          (toSheafify (SmallEtale.topology B Y.obj Y.property)
            ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F))) ≫
      (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}).map
          ((modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).map
            (fShriekModSheafifyIso.{u, v, max (u + 1) v} B Λ f F).inv) ≫
        (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}).map
          (((modShriekStalkIso.{u, v, max (u + 1) v} B Λ f s).app F).hom) =
    ((geometricPointSitePoint B Y.obj Y.property s).presheafFiberCompIso
          (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v})).inv.app
        ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F) ≫
      (finiteSupportStalkIso B f s ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F)
        (fun _ => inferInstance)).hom
  refine Eq.trans (congrArg (fun m =>
    (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}).map
        ((geometricPointSitePoint B Y.obj Y.property s).presheafFiber.map
          (toSheafify (SmallEtale.topology B Y.obj Y.property)
            ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F))) ≫
      (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}).map
          ((modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).map
            (fShriekModSheafifyIso.{u, v, max (u + 1) v} B Λ f F).inv) ≫ m)
    (forget₂_map_modShriekStalkIso_app_hom B Λ f s F)) ?_
  refine Eq.trans (congrArg (fun m =>
    (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}).map
        ((geometricPointSitePoint B Y.obj Y.property s).presheafFiber.map
          (toSheafify (SmallEtale.topology B Y.obj Y.property)
            ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F))) ≫ m)
    (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun m => m ≫ (fShriekStalkIso B f s
    ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F)).hom) key) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact congrArg (fun m =>
    ((geometricPointSitePoint B Y.obj Y.property s).presheafFiberCompIso
          (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v})).inv.app
        ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F) ≫ m)
    (fShriekStalkIso_comp_sheafification B f s
      ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F))

/-- **The stalk of the comparison map of the projection formula.** The stalk at `ȳ` of
`AlgebraicGeometry.SmallEtale.modFShriekProjectionMap` is the fibre comparison
`AlgebraicGeometry.SmallEtale.modProjectionFiberIso`, read through the identifications of both
sides with the fibres of sheafifications. -/
public theorem modStalkFunctor_map_modFShriekProjectionMap (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) :
    (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).map
        (modFShriekProjectionMap B Λ f F G) =
      (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).map
          (fShriekModTensorSheafifyIso B Λ f F G).hom ≫
        ((modSheafifyStalkIso.{u, v} B Λ Y s).hom.app
            ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F ⊗ G.obj) ≫
          (modProjectionFiberIso.{u, v} B Λ f s F G).hom ≫
            (modSheafifyStalkIso.{u, v} B Λ Y s).inv.app
              ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj
                (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G))) ≫
        (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).map
          (fShriekModSheafifyIso.{u, v, max (u + 1) v} B Λ f
            (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G)).inv := by
  change (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).map
      ((fShriekModTensorSheafifyIso B Λ f F G).hom ≫
        (presheafToSheaf (SmallEtale.topology B Y.obj Y.property)
            (ModuleCat.{max (u + 1) v} Λ)).map
          (modFiniteSupportTensorPresheafMap B Λ f F G) ≫
        (fShriekModSheafifyIso.{u, v, max (u + 1) v} B Λ f
          (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G)).inv) = _
  rw [Functor.map_comp, Functor.map_comp, modStalkFunctor_map_presheafToSheaf_map,
    presheafFiber_map_modFiniteSupportTensorPresheafMap]

/-- **The tensorator of the stalk functor against the identification of `f_!F ⊗_Λ G` with a
sheafification.** -/
public theorem modStalkFunctor_μ_fShriekModTensorSheafifyIso (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) :
    Functor.LaxMonoidal.μ (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s)
          ((fShriekMod.{u, v, max (u + 1) v} B Λ f).obj F) G ≫
        (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).map
            (fShriekModTensorSheafifyIso B Λ f F G).hom ≫
          (modSheafifyStalkIso.{u, v} B Λ Y s).hom.app
            ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F ⊗ G.obj) =
      (((modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).map
              (fShriekModSheafifyIso.{u, v, max (u + 1) v} B Λ f F).hom ≫
            (modSheafifyStalkIso.{u, v} B Λ Y s).hom.app
              ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F)) ⊗ₘ
          𝟙 ((modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj G)) ≫
        Functor.LaxMonoidal.μ ((geometricPointSitePoint B Y.obj Y.property s).presheafFiber)
          ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F) G.obj := by
  have hmon := NatTrans.IsMonoidal.tensor
    (τ := (modSheafifyStalkIso.{u, v} B Λ Y s).hom)
    ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F) G.obj
  rw [Functor.LaxMonoidal.comp_μ] at hmon
  simp only [Category.assoc] at hmon
  have hSh : (fShriekModTensorSheafifyIso B Λ f F G).hom =
      ((fShriekModSheafifyIso.{u, v, max (u + 1) v} B Λ f F).hom ⊗ₘ
          (asIso ((sheafificationAdjunction (SmallEtale.topology B Y.obj Y.property)
            (ModuleCat.{max (u + 1) v} Λ)).counit.app G)).symm.hom) ≫
        Functor.LaxMonoidal.μ (presheafToSheaf (SmallEtale.topology B Y.obj Y.property)
            (ModuleCat.{max (u + 1) v} Λ))
          ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F) G.obj := rfl
  rw [hSh, Functor.map_comp]
  simp only [Category.assoc]
  rw [← Functor.LaxMonoidal.μ_natural_assoc]
  refine (congrArg (fun m =>
    ((modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).map
          (fShriekModSheafifyIso.{u, v, max (u + 1) v} B Λ f F).hom ⊗ₘ
        (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).map
          (asIso ((sheafificationAdjunction (SmallEtale.topology B Y.obj Y.property)
            (ModuleCat.{max (u + 1) v} Λ)).counit.app G)).symm.hom) ≫ m) hmon).trans ?_
  rw [← Category.assoc, tensorHom_comp_tensorHom,
    modStalkFunctor_map_counit_symm_hom_comp]
  rfl

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- **The summand of the fibre comparison of the projection formula is the summand of the stalk
comparison.** -/
public theorem modProjectionFiberSummandIso_eq (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) (x : GeometricFiberPoint B f s) :
    modProjectionFiberSummandIso.{u, v} B Λ f s F G x =
      stalkFiberSummandIso.{u, v} B Λ f s F G x := by
  refine Iso.ext ?_
  change ((Iso.refl ((modStalkFunctor.{u, v, max (u + 1) v} B Λ X
            (x.toGeometricPoint B f s)).obj F)).hom ⊗ₘ
        (stalkPullbackFiberIso.{u, v} B Λ f s G x).hom) ≫
      Functor.LaxMonoidal.μ ((geometricPointSitePoint B X.obj X.property
            (x.toGeometricPoint B f s)).presheafFiber) F.obj
          ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G).obj ≫
        (geometricPointSitePoint B X.obj X.property
            (x.toGeometricPoint B f s)).presheafFiber.map
          (Stacks.ModuleSheafTensorSection.moduleToTensorSection
            (SmallEtale.topology B X.obj X.property) Λ F
            ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G)) =
    ((Iso.refl ((modStalkFunctor.{u, v, max (u + 1) v} B Λ X
            (x.toGeometricPoint B f s)).obj F)).hom ⊗ₘ
        (stalkPullbackFiberIso.{u, v} B Λ f s G x).hom) ≫
      Functor.LaxMonoidal.μ (modStalkFunctor.{u, v, max (u + 1) v} B Λ X
          (x.toGeometricPoint B f s)) F ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G)
  rw [modStalkFunctor_μ]
  rfl

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- The summandwise fibre comparison of the projection formula is the summandwise stalk
comparison. -/
public theorem modProjectionFiberSummandsIso_eq (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) :
    modProjectionFiberSummandsIso.{u, v} B Λ f s F G =
      modFiberStalksSummandsIso.{u, v} B Λ f s F G := by
  simp only [modProjectionFiberSummandsIso, modFiberStalksSummandsIso,
    modProjectionFiberSummandIso_eq]

/-- **The germ decomposition of the fibre of `f_{p!}F` is the stalk decomposition of `f_!F`**,
read through the identification of `f_!F` with the sheafification of `f_{p!}F`. -/
public theorem modStalkFunctor_map_fShriekModSheafifyIso_comp (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ) :
    (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).map
          (fShriekModSheafifyIso.{u, v, max (u + 1) v} B Λ f F).hom ≫
        (modSheafifyStalkIso.{u, v} B Λ Y s).hom.app
            ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F) ≫
          (modFiniteSupportFiberIso B Λ f F s).hom =
      ((modShriekStalkIso.{u, v, max (u + 1) v} B Λ f s).app F).hom := by
  rw [← presheafFiberModFiniteSupportStalkIso_eq]
  change (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).map
        (fShriekModSheafifyIso.{u, v, max (u + 1) v} B Λ f F).hom ≫
      (modSheafifyStalkIso.{u, v} B Λ Y s).hom.app
          ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F) ≫
        ((modSheafifyStalkIso.{u, v} B Λ Y s).inv.app
            ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F) ≫
          (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).map
              (fShriekModSheafifyIso.{u, v, max (u + 1) v} B Λ f F).inv ≫
            ((modShriekStalkIso.{u, v, max (u + 1) v} B Λ f s).app F).hom) = _
  rw [Iso.hom_inv_id_app_assoc, ← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- The fibre of the sheafification unit, followed by the stalk decomposition of `f_!F`, is the
germ decomposition of the fibre of `f_{p!}F`. -/
public theorem modSheafifyStalkIso_inv_app_comp_modShriekStalkIso (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ) :
    (modSheafifyStalkIso.{u, v} B Λ Y s).inv.app
          ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F) ≫
        (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).map
            (fShriekModSheafifyIso.{u, v, max (u + 1) v} B Λ f F).inv ≫
          ((modShriekStalkIso.{u, v, max (u + 1) v} B Λ f s).app F).hom =
      (modFiniteSupportFiberIso B Λ f F s).hom :=
  congrArg Iso.hom (presheafFiberModFiniteSupportStalkIso_eq B Λ f s F)

/-- The reassociated form of
`AlgebraicGeometry.SmallEtale.modSheafifyStalkIso_inv_app_comp_modShriekStalkIso`. -/
public theorem modSheafifyStalkIso_inv_app_comp_modShriekStalkIso_assoc
    (s : GeometricPoint Y.obj) (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    {Z : ModuleCat.{max (u + 1) v} Λ}
    (g : (moduleFiberStalks.{u, v, max (u + 1) v} B Λ f s).obj F ⟶ Z) :
    (modSheafifyStalkIso.{u, v} B Λ Y s).inv.app
          ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F) ≫
        (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).map
            (fShriekModSheafifyIso.{u, v, max (u + 1) v} B Λ f F).inv ≫
          ((modShriekStalkIso.{u, v, max (u + 1) v} B Λ f s).app F).hom ≫ g =
      (modFiniteSupportFiberIso B Λ f F s).hom ≫ g :=
  (reassoc_of% (modSheafifyStalkIso_inv_app_comp_modShriekStalkIso B Λ f s F)) g

/-- The reassociated form of
`AlgebraicGeometry.SmallEtale.modStalkFunctor_map_fShriekModSheafifyIso_comp`. -/
public theorem modStalkFunctor_map_fShriekModSheafifyIso_comp_assoc
    (s : GeometricPoint Y.obj) (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    {Z : ModuleCat.{max (u + 1) v} Λ}
    (g : (moduleFiberStalks.{u, v, max (u + 1) v} B Λ f s).obj F ⟶ Z) :
    (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).map
          (fShriekModSheafifyIso.{u, v, max (u + 1) v} B Λ f F).hom ≫
        (modSheafifyStalkIso.{u, v} B Λ Y s).hom.app
            ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F) ≫
          (modFiniteSupportFiberIso B Λ f F s).hom ≫ g =
      ((modShriekStalkIso.{u, v, max (u + 1) v} B Λ f s).app F).hom ≫ g :=
  (reassoc_of% (modStalkFunctor_map_fShriekModSheafifyIso_comp B Λ f s F)) g

/-- The reassociated form of
`AlgebraicGeometry.SmallEtale.modStalkFunctor_μ_fShriekModTensorSheafifyIso`. -/
public theorem modStalkFunctor_μ_fShriekModTensorSheafifyIso_assoc (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) {Z : ModuleCat.{max (u + 1) v} Λ}
    (g : (geometricPointSitePoint B Y.obj Y.property s).presheafFiber.obj
      ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F ⊗ G.obj) ⟶ Z) :
    Functor.LaxMonoidal.μ (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s)
          ((fShriekMod.{u, v, max (u + 1) v} B Λ f).obj F) G ≫
        (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).map
            (fShriekModTensorSheafifyIso B Λ f F G).hom ≫
          (modSheafifyStalkIso.{u, v} B Λ Y s).hom.app
            ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F ⊗ G.obj) ≫ g =
      (((modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).map
              (fShriekModSheafifyIso.{u, v, max (u + 1) v} B Λ f F).hom ≫
            (modSheafifyStalkIso.{u, v} B Λ Y s).hom.app
              ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F)) ⊗ₘ
          𝟙 ((modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj G)) ≫
        Functor.LaxMonoidal.μ ((geometricPointSitePoint B Y.obj Y.property s).presheafFiber)
          ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F) G.obj ≫ g :=
  (reassoc_of% (modStalkFunctor_μ_fShriekModTensorSheafifyIso B Λ f s F G)) g

/-- `AlgebraicGeometry.SmallEtale.modStalkFunctor_map_fShriekModSheafifyIso_comp`, followed by
`AlgebraicGeometry.SmallEtale.moduleFiberStalksIso` and bracketed in pairs. -/
public theorem modStalkFunctor_map_fShriekModSheafifyIso_comp_comp (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ) :
    ((modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).map
            (fShriekModSheafifyIso.{u, v, max (u + 1) v} B Λ f F).hom ≫
          (modSheafifyStalkIso.{u, v} B Λ Y s).hom.app
            ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F)) ≫
        ((modFiniteSupportFiberIso B Λ f F s).hom ≫
          (moduleFiberStalksIso.{u, v, max (u + 1) v} B Λ f s F).hom) =
      ((modShriekStalkIso.{u, v, max (u + 1) v} B Λ f s).app F).hom ≫
        (moduleFiberStalksIso.{u, v, max (u + 1) v} B Λ f s F).hom := by
  simp only [Category.assoc]
  rw [modStalkFunctor_map_fShriekModSheafifyIso_comp_assoc]

/-- The fibre comparison of the projection formula, written out. -/
public theorem modProjectionFiberIso_hom_eq (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) :
    (modProjectionFiberIso.{u, v} B Λ f s F G).hom =
      (Functor.Monoidal.μIso ((geometricPointSitePoint B Y.obj Y.property s).presheafFiber)
            ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F) G.obj).inv ≫
        (((modFiniteSupportFiberIso B Λ f F s).hom ≫
              (moduleFiberStalksIso.{u, v, max (u + 1) v} B Λ f s F).hom) ⊗ₘ
            𝟙 ((modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj G)) ≫
          (modFiberStalksTensorIso.{u, v} B Λ f s F
              ((modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj G)).hom ≫
            (modProjectionFiberSummandsIso.{u, v} B Λ f s F G).hom ≫
              (moduleFiberStalksIso.{u, v, max (u + 1) v} B Λ f s
                  (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G)).inv ≫
                (modFiniteSupportFiberIso B Λ f
                  (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G) s).inv :=
  rfl

/-- **The stalk of the comparison map of the projection formula, through the stalk decomposition
of `f_!`.** At a geometric point `ȳ` of `Y` the stalk of
`AlgebraicGeometry.SmallEtale.modFShriekProjectionMap`, read through the decompositions of the
stalks of `f_!F ⊗_Λ G` and of `f_!(F ⊗_Λ f^{-1}G)` over the geometric fibre, is the chain of
`AlgebraicGeometry.SmallEtale.modShriekProjectionStalkIso`: distribute the tensor product over
the direct sum, then compare summandwise. This is the stalkwise identity of [Stacks, Tag 0GKF]. -/
public theorem modStalkFunctor_μ_comp_modFShriekProjectionMap (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) :
    Functor.LaxMonoidal.μ (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s)
          ((fShriekMod.{u, v, max (u + 1) v} B Λ f).obj F) G ≫
        (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).map
            (modFShriekProjectionMap B Λ f F G) ≫
          ((modShriekStalkIso.{u, v, max (u + 1) v} B Λ f s).app
                (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G)).hom ≫
            (moduleFiberStalksIso.{u, v, max (u + 1) v} B Λ f s
              (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G)).hom =
      ((((modShriekStalkIso.{u, v, max (u + 1) v} B Λ f s).app F).hom ≫
            (moduleFiberStalksIso.{u, v, max (u + 1) v} B Λ f s F).hom) ⊗ₘ
          𝟙 ((modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj G)) ≫
        (modFiberStalksTensorIso.{u, v} B Λ f s F
            ((modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj G)).hom ≫
          (modFiberStalksSummandsIso.{u, v} B Λ f s F G).hom := by
  rw [modStalkFunctor_map_modFShriekProjectionMap, modProjectionFiberIso_hom_eq]
  simp only [Category.assoc]
  rw [modSheafifyStalkIso_inv_app_comp_modShriekStalkIso_assoc, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, Category.comp_id, modStalkFunctor_μ_fShriekModTensorSheafifyIso_assoc,
    ← Functor.Monoidal.μIso_hom]
  have hcancel : (Functor.Monoidal.μIso
            ((geometricPointSitePoint B Y.obj Y.property s).presheafFiber)
            ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F) G.obj).hom ≫
        (Functor.Monoidal.μIso ((geometricPointSitePoint B Y.obj Y.property s).presheafFiber)
            ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F) G.obj).inv ≫
          ((((modFiniteSupportFiberIso B Λ f F s).hom ≫
                  (moduleFiberStalksIso.{u, v, max (u + 1) v} B Λ f s F).hom) ⊗ₘ
              𝟙 ((modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj G)) ≫
            (modFiberStalksTensorIso.{u, v} B Λ f s F
                ((modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj G)).hom ≫
              (modProjectionFiberSummandsIso.{u, v} B Λ f s F G).hom) =
      ((((modFiniteSupportFiberIso B Λ f F s).hom ≫
              (moduleFiberStalksIso.{u, v, max (u + 1) v} B Λ f s F).hom) ⊗ₘ
          𝟙 ((modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj G)) ≫
        (modFiberStalksTensorIso.{u, v} B Λ f s F
            ((modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj G)).hom ≫
          (modProjectionFiberSummandsIso.{u, v} B Λ f s F G).hom) :=
    Iso.hom_inv_id_assoc _ _
  refine (congrArg (fun m =>
    ((modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).map
            (fShriekModSheafifyIso.{u, v, max (u + 1) v} B Λ f F).hom ≫
          (modSheafifyStalkIso.{u, v} B Λ Y s).hom.app
            ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F) ⊗ₘ
        𝟙 ((modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj G)) ≫ m) hcancel).trans ?_
  rw [tensorHom_comp_tensorHom_assoc, Category.comp_id,
    modStalkFunctor_map_fShriekModSheafifyIso_comp_comp]
  exact congrArg (fun m =>
    ((((modShriekStalkIso.{u, v, max (u + 1) v} B Λ f s).app F).hom ≫
          (moduleFiberStalksIso.{u, v, max (u + 1) v} B Λ f s F).hom) ⊗ₘ
        𝟙 ((modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj G)) ≫
      (modFiberStalksTensorIso.{u, v} B Λ f s F
          ((modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj G)).hom ≫
        Iso.hom m) (modProjectionFiberSummandsIso_eq B Λ f s F G)

/-- `AlgebraicGeometry.SmallEtale.modStalkFunctor_μ_comp_modFShriekProjectionMap`, written with
`AlgebraicGeometry.SmallEtale.modShriekFiberStalksIso`. -/
public theorem modStalkFunctor_μ_comp_modFShriekProjectionMap'
    (s : GeometricPoint Y.obj) (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) :
    Functor.LaxMonoidal.μ (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s)
          ((fShriekMod.{u, v, max (u + 1) v} B Λ f).obj F) G ≫
        (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).map
            (modFShriekProjectionMap B Λ f F G) ≫
          (modShriekFiberStalksIso.{u, v} B Λ f s
            (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G)).hom =
      ((modShriekFiberStalksIso.{u, v} B Λ f s F).hom ⊗ₘ
          𝟙 ((modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj G)) ≫
        (modFiberStalksTensorIso.{u, v} B Λ f s F
            ((modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj G)).hom ≫
          (modFiberStalksSummandsIso.{u, v} B Λ f s F G).hom :=
  modStalkFunctor_μ_comp_modFShriekProjectionMap B Λ f s F G

end FiniteSupportFiberComparison

/-- **The projection formula at the constant sheaf**, `f_!(𝟙_) ⊗_Λ G ≅ f_!(f^{-1}G)`: the
projection isomorphism `AlgebraicGeometry.SmallEtale.modFShriekProjectionIso` of
[Stacks, Tag 0GKF] with `F` the unit, followed by the left unitor inside `f_!`. -/
public def modShriekUnitTensorIso (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) :
    (fShriekMod.{u, v, max (u + 1) v} B Λ f).obj (𝟙_ _) ⊗ G ≅
      (fShriekMod.{u, v, max (u + 1) v} B Λ f).obj
        ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G) :=
  modFShriekProjectionIso.{u, v} B Λ f (𝟙_ _) G ≪≫
    (fShriekMod.{u, v, max (u + 1) v} B Λ f).mapIso
      (λ_ ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G))

/-- **The trace of [Stacks, Tag 0GKG]**: from a trace `Tr : f_!(𝟙_) ⟶ 𝟙_` on the constant sheaf,
the trace `f_!(f^{-1}G) ⟶ G` on an arbitrary sheaf of `Λ`-modules `G` on `Y_étale`, obtained by
tensoring `Tr` with `G` and reading both ends through the projection formula and the left
unitor. -/
public def modWeightedTrace (Tr : (fShriekMod.{u, v, max (u + 1) v} B Λ f).obj (𝟙_ _) ⟶ 𝟙_ _)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) :
    (fShriekMod.{u, v, max (u + 1) v} B Λ f).obj
        ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G) ⟶ G :=
  (modShriekUnitTensorIso.{u, v} B Λ f G).inv ≫ (Tr ⊗ₘ 𝟙 G) ≫ (λ_ G).hom

/-- **The summand of the weighted sum on the constant sheaf** indexed by a point `x̄` of the
geometric fibre of `f` above a geometric point `ȳ` of `Y`: the stalk of the unit at `x̄` is
canonically `Λ`, and is multiplied by the weight `w(x̄)` and carried to the stalk of the unit at
`ȳ`, again canonically `Λ`. -/
public def modUnitWeightedSumSummand (w : X.obj → ℤ) (s : GeometricPoint Y.obj)
    (x : GeometricFiberPoint B f s) :
    ((modStalkFunctor.{u, v, max (u + 1) v} B Λ X (x.toGeometricPoint B f s)).obj
        (𝟙_ _) : Type _) →ₗ[Λ]
      ((modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj (𝟙_ _) : Type _) :=
  w (x.1 default) •
    ((Functor.Monoidal.εIso
          (modStalkFunctor.{u, v, max (u + 1) v} B Λ X (x.toGeometricPoint B f s))).inv ≫
        (Functor.Monoidal.εIso (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s)).hom).hom

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- The summand of `AlgebraicGeometry.SmallEtale.modUnitWeightedSum` on an element: the stalk of
the unit at `x̄` is read into `Λ`, multiplied by the weight `w(x̄)` and read back into the stalk
of the unit at `ȳ`. -/
public theorem modUnitWeightedSumSummand_apply (w : X.obj → ℤ) (s : GeometricPoint Y.obj)
    (x : GeometricFiberPoint B f s)
    (a : (modStalkFunctor.{u, v, max (u + 1) v} B Λ X (x.toGeometricPoint B f s)).obj (𝟙_ _)) :
    modUnitWeightedSumSummand.{u, v} B Λ f w s x a =
      w (x.1 default) •
        (Functor.Monoidal.εIso (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s)).hom
          ((Functor.Monoidal.εIso (modStalkFunctor.{u, v, max (u + 1) v} B Λ X
            (x.toGeometricPoint B f s))).inv a) :=
  rfl

/-- **The weighted sum over the geometric fibre on the constant sheaf**, assembled from its
summands by the universal property of the direct sum. -/
public def modUnitWeightedSum (w : X.obj → ℤ) (s : GeometricPoint Y.obj) :
    modFiberStalks.{u, v, max (u + 1) v} B Λ f s (𝟙_ _) ⟶
      (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj (𝟙_ _) :=
  letI : DecidableEq (GeometricFiberPoint B f s) := Classical.decEq _
  ModuleCat.ofHom (DirectSum.toModule Λ (GeometricFiberPoint B f s) _
    (modUnitWeightedSumSummand.{u, v} B Λ f w s))

/-- **The summand of the weighted sum over the geometric fibre** indexed by a point `x̄` of that
fibre: the weight `w(x̄)` times the identification of the stalk of `f^{-1}G` at `x̄` with the
stalk of `G` at `ȳ` of Stacks 03Q1. -/
public def modWeightedTraceStalkSummand (w : X.obj → ℤ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) (s : GeometricPoint Y.obj)
    (x : GeometricFiberPoint B f s) :
    ((modStalkFunctor.{u, v, max (u + 1) v} B Λ X (x.toGeometricPoint B f s)).obj
        ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G) : Type _) →ₗ[Λ]
      ((modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj G : Type _) :=
  w (x.1 default) • (stalkPullbackFiberIso.{u, v} B Λ f s G x).inv.hom

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- The summand of `AlgebraicGeometry.SmallEtale.modWeightedTraceStalkMap` on an element. -/
public theorem modWeightedTraceStalkSummand_apply (w : X.obj → ℤ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) (s : GeometricPoint Y.obj)
    (x : GeometricFiberPoint B f s)
    (a : (modStalkFunctor.{u, v, max (u + 1) v} B Λ X (x.toGeometricPoint B f s)).obj
      ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G)) :
    modWeightedTraceStalkSummand.{u, v} B Λ f w G s x a =
      w (x.1 default) • (stalkPullbackFiberIso.{u, v} B Λ f s G x).inv a :=
  rfl

/-- **The weighted sum over the geometric fibre.** The summand indexed by a point `x̄` of the
geometric fibre of `f` above a geometric point `ȳ` of `Y` is the stalk of `f^{-1}G` at `x̄`,
which is the stalk of `G` at `ȳ` by Stacks 03Q1; it is multiplied by the weight `w(x̄)`. -/
public def modWeightedTraceStalkMap (w : X.obj → ℤ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) (s : GeometricPoint Y.obj) :
    modFiberStalks.{u, v, max (u + 1) v} B Λ f s
        ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G) ⟶
      (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj G :=
  letI : DecidableEq (GeometricFiberPoint B f s) := Classical.decEq _
  ModuleCat.ofHom (DirectSum.toModule Λ (GeometricFiberPoint B f s) _
    (modWeightedTraceStalkSummand.{u, v} B Λ f w G s))

/-- **The characterising property of the trace on the constant sheaf.** A morphism
`Tr : f_!(𝟙_) ⟶ 𝟙_` has weighted unit trace stalks if at every geometric point `ȳ` of `Y` the
map it induces on stalks, read through the decomposition of the stalk of `f_!(𝟙_)` into the
direct sum over the geometric fibre above `ȳ`, is the weighted sum of
`AlgebraicGeometry.SmallEtale.modUnitWeightedSum`. -/
public def ModHasUnitTraceStalks (w : X.obj → ℤ)
    (Tr : (fShriekMod.{u, v, max (u + 1) v} B Λ f).obj (𝟙_ _) ⟶ 𝟙_ _) : Prop :=
  ∀ s : GeometricPoint Y.obj,
    ((modShriekStalkIso.{u, v, max (u + 1) v} B Λ f s).app (𝟙_ _) ≪≫
          moduleFiberStalksIso.{u, v, max (u + 1) v} B Λ f s (𝟙_ _)).inv ≫
        (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).map Tr =
      modUnitWeightedSum.{u, v} B Λ f w s

/-- **The characterising property of the trace of [Stacks, Tag 0GKG].** A morphism
`τ : f_!(f^{-1}G) ⟶ G` has weighted trace stalks if at every geometric point `ȳ` of `Y` the map
it induces on stalks, read through the decomposition of the stalk of `f_!(f^{-1}G)` into the
direct sum of the stalks of `f^{-1}G` over the geometric fibre above `ȳ`, is the weighted sum of
`AlgebraicGeometry.SmallEtale.modWeightedTraceStalkMap`. -/
public def ModHasWeightedTraceStalks (w : X.obj → ℤ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ)
    (τ : (fShriekMod.{u, v, max (u + 1) v} B Λ f).obj
      ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G) ⟶ G) : Prop :=
  ∀ s : GeometricPoint Y.obj,
    ((modShriekStalkIso.{u, v, max (u + 1) v} B Λ f s).app
            ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G) ≪≫
          moduleFiberStalksIso.{u, v, max (u + 1) v} B Λ f s
            ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G)).inv ≫
        (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).map τ =
      modWeightedTraceStalkMap.{u, v} B Λ f w G s

/-- **The summand of the direct sum of stalks over the geometric fibre** indexed by a point `x̄`
of that fibre. -/
public def modFiberStalkOf (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ) (x : GeometricFiberPoint B f s) :
    (modStalkFunctor.{u, v, max (u + 1) v} B Λ X (x.toGeometricPoint B f s)).obj F ⟶
      modFiberStalks.{u, v, max (u + 1) v} B Λ f s F := by
  letI : DecidableEq (GeometricFiberPoint B f s) := Classical.decEq _
  exact ModuleCat.ofHom (DirectSum.lof Λ (GeometricFiberPoint B f s)
    (fun y : GeometricFiberPoint B f s =>
      ((modStalkFunctor.{u, v, max (u + 1) v} B Λ X (y.toGeometricPoint B f s)).obj F : Type _)) x)

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- Two maps out of the direct sum of the stalks over the geometric fibre agree as soon as they
agree on every summand. -/
public theorem modFiberStalks_hom_ext (s : GeometricPoint Y.obj)
    {F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ} {M : ModuleCat.{max (u + 1) v} Λ}
    {g h : modFiberStalks.{u, v, max (u + 1) v} B Λ f s F ⟶ M}
    (H : ∀ (x : GeometricFiberPoint B f s)
      (z : (modStalkFunctor.{u, v, max (u + 1) v} B Λ X (x.toGeometricPoint B f s)).obj F),
      g (modFiberStalkOf.{u, v} B Λ f s F x z) = h (modFiberStalkOf.{u, v} B Λ f s F x z)) :
    g = h := by
  let : DecidableEq (GeometricFiberPoint B f s) := Classical.decEq _
  exact ModuleCat.hom_ext (DirectSum.linearMap_ext Λ fun x =>
    LinearMap.ext fun z => H x z)

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- **The weighted sum on the constant sheaf, on a summand**: the summand indexed by `x̄` is
multiplied by the weight `w(x̄)` and read from `Λ` back into the stalk of the unit at `ȳ`. -/
public theorem modUnitWeightedSum_modFiberStalkOf (w : X.obj → ℤ) (s : GeometricPoint Y.obj)
    (x : GeometricFiberPoint B f s)
    (a : (modStalkFunctor.{u, v, max (u + 1) v} B Λ X (x.toGeometricPoint B f s)).obj (𝟙_ _)) :
    modUnitWeightedSum.{u, v} B Λ f w s (modFiberStalkOf.{u, v} B Λ f s (𝟙_ _) x a) =
      modUnitWeightedSumSummand.{u, v} B Λ f w s x a := by
  let : DecidableEq (GeometricFiberPoint B f s) := Classical.decEq _
  exact DirectSum.toModule_lof (φ := modUnitWeightedSumSummand.{u, v} B Λ f w s) Λ x a

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- **The weighted sum over the geometric fibre, on a summand**: the summand indexed by `x̄` is
multiplied by the weight `w(x̄)` and carried to the stalk of `G` at `ȳ` by Stacks 03Q1. -/
public theorem modWeightedTraceStalkMap_modFiberStalkOf (w : X.obj → ℤ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) (s : GeometricPoint Y.obj)
    (x : GeometricFiberPoint B f s)
    (a : (modStalkFunctor.{u, v, max (u + 1) v} B Λ X (x.toGeometricPoint B f s)).obj
      ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G)) :
    modWeightedTraceStalkMap.{u, v} B Λ f w G s
        (modFiberStalkOf.{u, v} B Λ f s ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G) x a) =
      modWeightedTraceStalkSummand.{u, v} B Λ f w G s x a := by
  let : DecidableEq (GeometricFiberPoint B f s) := Classical.decEq _
  exact DirectSum.toModule_lof (φ := modWeightedTraceStalkSummand.{u, v} B Λ f w G s) Λ x a

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- **The weighted sum on the constant sheaf, read into `Λ`.** Composing
`AlgebraicGeometry.SmallEtale.modUnitWeightedSum` with the unit comparison of the stalk functor
on `Y` leaves, on the summand indexed by `x̄`, the weight `w(x̄)` times the unit comparison of the
stalk functor at `x̄`. -/
public theorem εIso_inv_modUnitWeightedSum_modFiberStalkOf (w : X.obj → ℤ)
    (s : GeometricPoint Y.obj) (x : GeometricFiberPoint B f s)
    (a : (modStalkFunctor.{u, v, max (u + 1) v} B Λ X (x.toGeometricPoint B f s)).obj (𝟙_ _)) :
    (Functor.Monoidal.εIso (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s)).inv
        (modUnitWeightedSum.{u, v} B Λ f w s
          (modFiberStalkOf.{u, v} B Λ f s (𝟙_ _) x a)) =
      w (x.1 default) •
        (Functor.Monoidal.εIso (modStalkFunctor.{u, v, max (u + 1) v} B Λ X
          (x.toGeometricPoint B f s))).inv a := by
  rw [modUnitWeightedSum_modFiberStalkOf, modUnitWeightedSumSummand_apply, map_zsmul,
    Iso.hom_inv_id_apply]

/-- **Tensoring the trace on the constant sheaf with `G` and applying the left unitor, on a
stalk.** The stalk functor is monoidal, so on the stalk at `ȳ` the map `Tr ⊗ 1` followed by the
left unitor is the stalk of `Tr`, read into `Λ` by the unit comparison, acting on the left factor
of `Λ ⊗ G_ȳ`. -/
public theorem modStalkFunctor_map_tensorHom_leftUnitor (s : GeometricPoint Y.obj)
    (Tr : (fShriekMod.{u, v, max (u + 1) v} B Λ f).obj (𝟙_ _) ⟶ 𝟙_ _)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) :
    (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).map ((Tr ⊗ₘ 𝟙 G) ≫ (λ_ G).hom) =
      (Functor.Monoidal.μIso (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s)
            ((fShriekMod.{u, v, max (u + 1) v} B Λ f).obj (𝟙_ _)) G).inv ≫
        ((modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).map Tr ≫
            (Functor.Monoidal.εIso
              (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s)).inv) ▷
          (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj G ≫
        (λ_ ((modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj G)).hom := by
  rw [Iso.eq_inv_comp, Functor.Monoidal.μIso_hom, Functor.map_comp, ← Category.assoc,
    ← Functor.LaxMonoidal.μ_natural, Category.assoc,
    Stacks.laxMonoidal_μ_comp_map_leftUnitor, CategoryTheory.Functor.map_id, tensorHom_id,
    ← Category.assoc, ← comp_whiskerRight]

/-- **The stalk of the trace of [Stacks, Tag 0GKG].** Reading the source through the projection
formula at the constant sheaf, the stalk of the trace is the stalk of `Tr` acting on the left
factor. -/
public theorem modStalkFunctor_map_modWeightedTrace (s : GeometricPoint Y.obj)
    (Tr : (fShriekMod.{u, v, max (u + 1) v} B Λ f).obj (𝟙_ _) ⟶ 𝟙_ _)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) :
    (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).map
        (modWeightedTrace.{u, v} B Λ f Tr G) =
      (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).map
          (modShriekUnitTensorIso.{u, v} B Λ f G).inv ≫
        (Functor.Monoidal.μIso (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s)
            ((fShriekMod.{u, v, max (u + 1) v} B Λ f).obj (𝟙_ _)) G).inv ≫
        ((modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).map Tr ≫
            (Functor.Monoidal.εIso
              (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s)).inv) ▷
          (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj G ≫
        (λ_ ((modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj G)).hom := by
  change (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).map
      ((modShriekUnitTensorIso.{u, v} B Λ f G).inv ≫ (Tr ⊗ₘ 𝟙 G) ≫ (λ_ G).hom) = _
  rw [Functor.map_comp, modStalkFunctor_map_tensorHom_leftUnitor B Λ f s Tr G]

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- **The summand of the stalk comparison of the projection formula at the constant sheaf,
against the left unitor.** On the summand indexed by a point `x̄` of the geometric fibre, the
comparison `(𝟙_)_x̄ ⊗ G_ȳ ≅ (𝟙_ ⊗ f^{-1}G)_x̄` followed by the stalk of the left unitor is the
left unitor of `G_ȳ`, after the stalk of the unit at `x̄` is read into `Λ`, followed by Stacks
03Q1 above `x̄`. -/
public theorem stalkFiberSummandIso_comp_map_leftUnitor (s : GeometricPoint Y.obj)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) (x : GeometricFiberPoint B f s) :
    (stalkFiberSummandIso.{u, v} B Λ f s (𝟙_ _) G x).hom ≫
        (modStalkFunctor.{u, v, max (u + 1) v} B Λ X (x.toGeometricPoint B f s)).map
          (λ_ ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G)).hom =
      (Functor.Monoidal.εIso (modStalkFunctor.{u, v, max (u + 1) v} B Λ X
              (x.toGeometricPoint B f s))).inv ▷
          (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj G ≫
        (λ_ ((modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj G)).hom ≫
          (stalkPullbackFiberIso.{u, v} B Λ f s G x).hom := by
  rw [stalkFiberSummandIso, Iso.trans_hom, Category.assoc, modStalkTensorIso,
    Functor.Monoidal.μIso_hom, Stacks.laxMonoidal_μ_comp_map_leftUnitor, tensorIso_hom,
    Iso.refl_hom, ← Category.assoc, ← tensorHom_id, tensorHom_comp_tensorHom,
    Category.id_comp, Category.comp_id, ← leftUnitor_naturality, ← tensorHom_id,
    ← id_tensorHom, ← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id,
    Category.id_comp]

/-- **The stalk of the comparison map of the projection formula**, read on the fibre of the
presheaf `f_{p!}F ⊗_Λ G` it was sheafified from: through the germ comparison
`CategoryTheory.toSheafify` of a presheaf with its sheafification, the stalk of
`AlgebraicGeometry.SmallEtale.modFShriekProjectionMap` is the fibre comparison
`AlgebraicGeometry.SmallEtale.modProjectionFiberIso`. -/
public theorem presheafFiber_toSheafify_modFShriekProjectionMap (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) :
    (geometricPointSitePoint B Y.obj Y.property s).presheafFiber.map
          (toSheafify (SmallEtale.topology B Y.obj Y.property)
            ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F ⊗ G.obj)) ≫
        (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).map
          ((fShriekModTensorSheafifyIso B Λ f F G).inv ≫
            modFShriekProjectionMap B Λ f F G ≫
            (fShriekModSheafifyIso.{u, v, max (u + 1) v} B Λ f
              (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G)).hom) =
      (modProjectionFiberIso.{u, v} B Λ f s F G).hom ≫
        (geometricPointSitePoint B Y.obj Y.property s).presheafFiber.map
          (toSheafify (SmallEtale.topology B Y.obj Y.property)
            ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj
              (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G))) := by
  have h0 : (fShriekModTensorSheafifyIso B Λ f F G).inv ≫
        modFShriekProjectionMap B Λ f F G ≫
        (fShriekModSheafifyIso.{u, v, max (u + 1) v} B Λ f
          (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G)).hom =
      (presheafToSheaf (SmallEtale.topology B Y.obj Y.property)
        (ModuleCat.{max (u + 1) v} Λ)).map (modFiniteSupportTensorPresheafMap B Λ f F G) := by
    change (fShriekModTensorSheafifyIso B Λ f F G).inv ≫
        ((fShriekModTensorSheafifyIso B Λ f F G).hom ≫
          (presheafToSheaf (SmallEtale.topology B Y.obj Y.property)
              (ModuleCat.{max (u + 1) v} Λ)).map
            (modFiniteSupportTensorPresheafMap B Λ f F G) ≫
          (fShriekModSheafifyIso.{u, v, max (u + 1) v} B Λ f
            (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G)).inv) ≫
        (fShriekModSheafifyIso.{u, v, max (u + 1) v} B Λ f
          (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G)).hom = _
    simp
  rw [h0, ← presheafFiber_map_modFiniteSupportTensorPresheafMap B Λ f s F G]
  change (geometricPointSitePoint B Y.obj Y.property s).presheafFiber.map
        (toSheafify (SmallEtale.topology B Y.obj Y.property)
          ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F ⊗ G.obj)) ≫
      (geometricPointSitePoint B Y.obj Y.property s).presheafFiber.map
        (((presheafToSheaf (SmallEtale.topology B Y.obj Y.property)
            (ModuleCat.{max (u + 1) v} Λ)).map
          (modFiniteSupportTensorPresheafMap B Λ f F G)).hom) = _
  rw [← Functor.map_comp, ← toSheafify_naturality, Functor.map_comp]

/-- **The summand of the direct sum of the `Λ`-module stalks over the geometric fibre**, in the
form `AlgebraicGeometry.SmallEtale.moduleFiberStalks` takes. -/
public def moduleFiberStalkOf (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ) (x : GeometricFiberPoint B f s) :
    (moduleEtaleStalkFunctor.{u, v, max (u + 1) v} B Λ X (x.toGeometricPoint B f s)).obj F ⟶
      (moduleFiberStalks.{u, v, max (u + 1) v} B Λ f s).obj F := by
  letI : DecidableEq (GeometricFiberPoint B f s) := Classical.decEq _
  exact ModuleCat.ofHom (DirectSum.lof Λ (GeometricFiberPoint B f s)
    (fun y : GeometricFiberPoint B f s =>
      ((moduleEtaleStalkFunctor.{u, v, max (u + 1) v} B Λ X
        (y.toGeometricPoint B f s)).obj F : Type _)) x)

/-- A summandwise linear equivalence of direct sums acts on a summand by the equivalence. -/
private theorem congrLinearEquiv_lof_apply {ι : Type*} [DecidableEq ι] {R : Type*} [Semiring R]
    {N P : ι → Type*} [∀ i, AddCommMonoid (N i)] [∀ i, AddCommMonoid (P i)]
    [∀ i, Module R (N i)] [∀ i, Module R (P i)] (e : ∀ i, N i ≃ₗ[R] P i) (i : ι) (z : N i) :
    DirectSum.congrLinearEquiv e (DirectSum.lof R ι N i z) = DirectSum.lof R ι P i (e i z) := by
  simp [DirectSum.coe_congrLinearEquiv, DirectSum.lmap_lof]

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- The identification of the two `Λ`-module structures on a stalk, on the summand indexed by a
point of the geometric fibre. -/
public theorem moduleFiberStalkOf_comp_moduleFiberStalksIso (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ) (x : GeometricFiberPoint B f s) :
    moduleFiberStalkOf.{u, v} B Λ f s F x ≫
        (moduleFiberStalksIso.{u, v, max (u + 1) v} B Λ f s F).hom =
      (moduleEtaleStalkIso.{u, v, max (u + 1) v} B Λ X
          (x.toGeometricPoint B f s)).hom.app F ≫
        modFiberStalkOf.{u, v} B Λ f s F x := by
  let : DecidableEq (GeometricFiberPoint B f s) := Classical.decEq _
  refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
  exact congrLinearEquiv_lof_apply (R := Λ)
    (N := fun y : GeometricFiberPoint B f s =>
      ((moduleEtaleStalkFunctor.{u, v, max (u + 1) v} B Λ X (y.toGeometricPoint B f s)).obj F :
        Type _))
    (P := fun y : GeometricFiberPoint B f s =>
      ((modStalkFunctor.{u, v, max (u + 1) v} B Λ X (y.toGeometricPoint B f s)).obj F : Type _))
    (fun y => ((moduleEtaleStalkIso.{u, v, max (u + 1) v} B Λ X
      (y.toGeometricPoint B f s)).app F).toLinearEquiv) x z

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- The map induced on the direct sum of the `Λ`-module stalks over the geometric fibre by a
morphism of sheaves of `Λ`-modules acts on the summand indexed by a point of the fibre by the
map on that stalk. -/
public theorem moduleFiberStalkOf_comp_moduleFiberStalks_map (s : GeometricPoint Y.obj)
    {F F' : ModuleSheaf.{u, v, max (u + 1) v} B X Λ} (φ : F ⟶ F')
    (x : GeometricFiberPoint B f s) :
    moduleFiberStalkOf.{u, v} B Λ f s F x ≫
        (moduleFiberStalks.{u, v, max (u + 1) v} B Λ f s).map φ =
      (moduleEtaleStalkFunctor.{u, v, max (u + 1) v} B Λ X
          (x.toGeometricPoint B f s)).map φ ≫
        moduleFiberStalkOf.{u, v} B Λ f s F' x := by
  refine (forget₂ (ModuleCat.{max (u + 1) v} Λ)
    AddCommGrpCat.{max (u + 1) v}).map_injective ?_
  rw [Functor.map_comp, Functor.map_comp]
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun z => ?_)
  exact fiberStalksMap_fiberStalkOf.{u, v} B f s
    ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).map φ) x z

/-- **The stalk decomposition of `f_!` is natural, summandwise.** The decomposition of the stalk
of `f_!F` at a geometric point `ȳ` of `Y` carries the map induced by `f_!φ` to the map `φ`
induces on the stalk at `x̄` of the summand indexed by `x̄`. -/
public theorem modFiberStalkOf_comp_modShriekStalkIso_naturality (s : GeometricPoint Y.obj)
    {F F' : ModuleSheaf.{u, v, max (u + 1) v} B X Λ} (φ : F ⟶ F')
    (x : GeometricFiberPoint B f s) :
    modFiberStalkOf.{u, v} B Λ f s F x ≫
        (moduleFiberStalksIso.{u, v, max (u + 1) v} B Λ f s F).inv ≫
          (modShriekStalkIso.{u, v, max (u + 1) v} B Λ f s).inv.app F ≫
            (fShriekMod.{u, v, max (u + 1) v} B Λ f ⋙
                modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).map φ ≫
              (modShriekStalkIso.{u, v, max (u + 1) v} B Λ f s).hom.app F' ≫
                (moduleFiberStalksIso.{u, v, max (u + 1) v} B Λ f s F').hom =
      (modStalkFunctor.{u, v, max (u + 1) v} B Λ X (x.toGeometricPoint B f s)).map φ ≫
        modFiberStalkOf.{u, v} B Λ f s F' x := by
  have hstep : modFiberStalkOf.{u, v} B Λ f s F x ≫
      (moduleFiberStalksIso.{u, v, max (u + 1) v} B Λ f s F).inv =
      (moduleEtaleStalkIso.{u, v, max (u + 1) v} B Λ X
            (x.toGeometricPoint B f s)).inv.app F ≫
        moduleFiberStalkOf.{u, v} B Λ f s F x := by
    rw [Iso.comp_inv_eq, Category.assoc, moduleFiberStalkOf_comp_moduleFiberStalksIso,
      Iso.inv_hom_id_app_assoc]
  have key : moduleFiberStalkOf.{u, v} B Λ f s F x ≫
      (moduleFiberStalks.{u, v, max (u + 1) v} B Λ f s).map φ ≫
        (moduleFiberStalksIso.{u, v, max (u + 1) v} B Λ f s F').hom =
      (moduleEtaleStalkFunctor.{u, v, max (u + 1) v} B Λ X
            (x.toGeometricPoint B f s)).map φ ≫
        (moduleEtaleStalkIso.{u, v, max (u + 1) v} B Λ X
            (x.toGeometricPoint B f s)).hom.app F' ≫
          modFiberStalkOf.{u, v} B Λ f s F' x := by
    rw [← Category.assoc, moduleFiberStalkOf_comp_moduleFiberStalks_map, Category.assoc,
      moduleFiberStalkOf_comp_moduleFiberStalksIso]
  rw [NatTrans.naturality_assoc, Iso.inv_hom_id_app_assoc, ← Category.assoc, hstep,
    Category.assoc, key, NatTrans.naturality_assoc, Iso.inv_hom_id_app_assoc]

/-- `AlgebraicGeometry.SmallEtale.modFiberStalkOf_comp_modShriekStalkIso_naturality`, written
with `AlgebraicGeometry.SmallEtale.modShriekFiberStalksIso`. -/
public theorem modFiberStalkOf_comp_modShriekFiberStalksIso_naturality (s : GeometricPoint Y.obj)
    {F F' : ModuleSheaf.{u, v, max (u + 1) v} B X Λ} (φ : F ⟶ F')
    (x : GeometricFiberPoint B f s) :
    modFiberStalkOf.{u, v} B Λ f s F x ≫
        (modShriekFiberStalksIso.{u, v} B Λ f s F).inv ≫
          (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).map
              ((fShriekMod.{u, v, max (u + 1) v} B Λ f).map φ) ≫
            (modShriekFiberStalksIso.{u, v} B Λ f s F').hom =
      (modStalkFunctor.{u, v, max (u + 1) v} B Λ X (x.toGeometricPoint B f s)).map φ ≫
        modFiberStalkOf.{u, v} B Λ f s F' x :=
  modFiberStalkOf_comp_modShriekStalkIso_naturality.{u, v} B Λ f s φ x

/-- **The summand of `⊕_{f(x̄) = ȳ} (F_x̄ ⊗_Λ N)`** indexed by a point `x̄` of the geometric
fibre. -/
public def modFiberStalksTensorOf (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ) (N : ModuleCat.{max (u + 1) v} Λ)
    (x : GeometricFiberPoint B f s) :
    ((modStalkFunctor.{u, v, max (u + 1) v} B Λ X (x.toGeometricPoint B f s)).obj F ⊗ N :
        ModuleCat.{max (u + 1) v} Λ) ⟶
      ModuleCat.of Λ (⨁ y : GeometricFiberPoint B f s,
        (((modStalkFunctor.{u, v, max (u + 1) v} B Λ X
          (y.toGeometricPoint B f s)).obj F ⊗ N : ModuleCat.{max (u + 1) v} Λ) : Type _)) := by
  letI : DecidableEq (GeometricFiberPoint B f s) := Classical.decEq _
  exact ModuleCat.ofHom (DirectSum.lof Λ (GeometricFiberPoint B f s)
    (fun y : GeometricFiberPoint B f s =>
      (((modStalkFunctor.{u, v, max (u + 1) v} B Λ X
        (y.toGeometricPoint B f s)).obj F ⊗ N : ModuleCat.{max (u + 1) v} Λ) : Type _)) x)

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- Two maps out of `⊕_{f(x̄) = ȳ} (F_x̄ ⊗_Λ N)` agree as soon as they agree on every summand. -/
public theorem modFiberStalksTensor_hom_ext (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ) (N : ModuleCat.{max (u + 1) v} Λ)
    {M : ModuleCat.{max (u + 1) v} Λ}
    {g h : ModuleCat.of Λ (⨁ y : GeometricFiberPoint B f s,
        (((modStalkFunctor.{u, v, max (u + 1) v} B Λ X
          (y.toGeometricPoint B f s)).obj F ⊗ N : ModuleCat.{max (u + 1) v} Λ) : Type _)) ⟶ M}
    (H : ∀ x : GeometricFiberPoint B f s,
      modFiberStalksTensorOf.{u, v} B Λ f s F N x ≫ g =
        modFiberStalksTensorOf.{u, v} B Λ f s F N x ≫ h) :
    g = h := by
  let : DecidableEq (GeometricFiberPoint B f s) := Classical.decEq _
  exact ModuleCat.hom_ext (DirectSum.linearMap_ext Λ fun x =>
    LinearMap.ext fun z => ConcreteCategory.congr_hom (H x) z)

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- **Distributing the tensor product over the direct sum, on a summand**: the inverse of
`AlgebraicGeometry.SmallEtale.modFiberStalksTensorIso` sends the pure tensor `a ⊗ n` in the
summand indexed by `x̄` to `a` placed in that summand, tensored with `n`. -/
public theorem modFiberStalksTensorIso_inv_modFiberStalksTensorOf (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ) (N : ModuleCat.{max (u + 1) v} Λ)
    (x : GeometricFiberPoint B f s)
    (a : (modStalkFunctor.{u, v, max (u + 1) v} B Λ X (x.toGeometricPoint B f s)).obj F)
    (n : N) :
    (modFiberStalksTensorIso.{u, v} B Λ f s F N).inv
        (modFiberStalksTensorOf.{u, v} B Λ f s F N x (a ⊗ₜ n)) =
      modFiberStalkOf.{u, v} B Λ f s F x a ⊗ₜ n := by
  let : DecidableEq (GeometricFiberPoint B f s) := Classical.decEq _
  exact TensorProduct.directSumLeft_symm_lof_tmul (R := Λ) (S := Λ)
    (M₁ := fun y : GeometricFiberPoint B f s =>
      ((modStalkFunctor.{u, v, max (u + 1) v} B Λ X (y.toGeometricPoint B f s)).obj F : Type _))
    (M₂' := ((N : Type _))) x a n

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- **The summandwise stalk comparison of the projection formula, on a summand.** -/
public theorem modFiberStalksSummandsIso_hom_modFiberStalksTensorOf (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) (x : GeometricFiberPoint B f s)
    (z : ((modStalkFunctor.{u, v, max (u + 1) v} B Λ X (x.toGeometricPoint B f s)).obj F ⊗
      (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj G : ModuleCat.{max (u + 1) v} Λ)) :
    (modFiberStalksSummandsIso.{u, v} B Λ f s F G).hom
        (modFiberStalksTensorOf.{u, v} B Λ f s F
          ((modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj G) x z) =
      modFiberStalkOf.{u, v} B Λ f s
          (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G) x
        ((stalkFiberSummandIso.{u, v} B Λ f s F G x).hom z) := by
  let : DecidableEq (GeometricFiberPoint B f s) := Classical.decEq _
  exact congrLinearEquiv_lof_apply (R := Λ)
    (fun y => (stalkFiberSummandIso.{u, v} B Λ f s F G y).toLinearEquiv) x z

/-- **The left unitor on the direct sum of stalks over the geometric fibre.** The map
`⊕_{f(x̄) = ȳ} (𝟙_ ⊗_Λ f^{-1}G)_x̄ ⟶ ⊕_{f(x̄) = ȳ} (f^{-1}G)_x̄` induced by the left unitor of
`f^{-1}G`, read through the stalk decomposition of `f_!`. -/
public def modFiberStalksLeftUnitor (s : GeometricPoint Y.obj)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) :
    modFiberStalks.{u, v, max (u + 1) v} B Λ f s
        (𝟙_ _ ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G) ⟶
      modFiberStalks.{u, v, max (u + 1) v} B Λ f s
        ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G) :=
  (modShriekFiberStalksIso.{u, v} B Λ f s
      (𝟙_ _ ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G)).inv ≫
    (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).map
        ((fShriekMod.{u, v, max (u + 1) v} B Λ f).map
          (λ_ ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G)).hom) ≫
      (modShriekFiberStalksIso.{u, v} B Λ f s
        ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G)).hom

/-- **The left unitor on the direct sum of stalks, on a summand**: it is the left unitor on the
stalk at `x̄`. -/
public theorem modFiberStalkOf_comp_modFiberStalksLeftUnitor (s : GeometricPoint Y.obj)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) (x : GeometricFiberPoint B f s) :
    modFiberStalkOf.{u, v} B Λ f s
          (𝟙_ _ ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G) x ≫
        modFiberStalksLeftUnitor.{u, v} B Λ f s G =
      (modStalkFunctor.{u, v, max (u + 1) v} B Λ X (x.toGeometricPoint B f s)).map
          (λ_ ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G)).hom ≫
        modFiberStalkOf.{u, v} B Λ f s
          ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G) x :=
  modFiberStalkOf_comp_modShriekFiberStalksIso_naturality.{u, v} B Λ f s
    (λ_ ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G)).hom x

/-- **The stalk of the projection formula at the constant sheaf.** -/
public theorem modStalkFunctor_μ_comp_modShriekUnitTensorIso (s : GeometricPoint Y.obj)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) :
    Functor.LaxMonoidal.μ (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s)
          ((fShriekMod.{u, v, max (u + 1) v} B Λ f).obj (𝟙_ _)) G ≫
        (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).map
            (modShriekUnitTensorIso.{u, v} B Λ f G).hom ≫
          (modShriekFiberStalksIso.{u, v} B Λ f s
            ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G)).hom =
      ((modShriekFiberStalksIso.{u, v} B Λ f s (𝟙_ _)).hom ⊗ₘ
          𝟙 ((modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj G)) ≫
        (modFiberStalksTensorIso.{u, v} B Λ f s (𝟙_ _)
            ((modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj G)).hom ≫
          (modFiberStalksSummandsIso.{u, v} B Λ f s (𝟙_ _) G).hom ≫
            modFiberStalksLeftUnitor.{u, v} B Λ f s G := by
  have h := (reassoc_of% (modStalkFunctor_μ_comp_modFShriekProjectionMap'.{u, v} B Λ f s
    (𝟙_ _) G)) (modFiberStalksLeftUnitor.{u, v} B Λ f s G)
  refine Eq.trans ?_ h
  change Functor.LaxMonoidal.μ (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s)
        ((fShriekMod.{u, v, max (u + 1) v} B Λ f).obj (𝟙_ _)) G ≫
      (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).map
          (modFShriekProjectionMap B Λ f (𝟙_ _) G ≫
            (fShriekMod.{u, v, max (u + 1) v} B Λ f).map
              (λ_ ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G)).hom) ≫
        (modShriekFiberStalksIso.{u, v} B Λ f s
          ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G)).hom = _
  rw [Functor.map_comp, modFiberStalksLeftUnitor]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- `AlgebraicGeometry.SmallEtale.εIso_inv_modUnitWeightedSum_modFiberStalkOf`, with the two
factors composed. -/
public theorem modUnitWeightedSum_comp_εIso_inv_modFiberStalkOf (w : X.obj → ℤ)
    (s : GeometricPoint Y.obj) (x : GeometricFiberPoint B f s)
    (a : (modStalkFunctor.{u, v, max (u + 1) v} B Λ X (x.toGeometricPoint B f s)).obj (𝟙_ _)) :
    (modUnitWeightedSum.{u, v} B Λ f w s ≫
          (Functor.Monoidal.εIso
            (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s)).inv)
        (modFiberStalkOf.{u, v} B Λ f s (𝟙_ _) x a) =
      w (x.1 default) •
        (Functor.Monoidal.εIso (modStalkFunctor.{u, v, max (u + 1) v} B Λ X
          (x.toGeometricPoint B f s))).inv a := by
  rw [← εIso_inv_modUnitWeightedSum_modFiberStalkOf]
  rfl

/-- **The weighted sum against the left unitor, on each summand of the geometric fibre.** This
is the computation [Stacks, Tag 0GKG] makes on stalks: on the summand indexed by `x̄`, the stalk
of the unit is `Λ`, the trace multiplies it by the weight `w(x̄)`, and the result acts on the
stalk of `G` at `ȳ`. -/
public theorem modFiberStalksTensorIso_inv_comp_modUnitWeightedSum (w : X.obj → ℤ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) (s : GeometricPoint Y.obj) :
    (modFiberStalksTensorIso.{u, v} B Λ f s (𝟙_ _)
            ((modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj G)).inv ≫
        ((modUnitWeightedSum.{u, v} B Λ f w s ≫
              (Functor.Monoidal.εIso
                (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s)).inv) ▷
            (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj G) ≫
          (λ_ ((modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj G)).hom =
      (modFiberStalksSummandsIso.{u, v} B Λ f s (𝟙_ _) G).hom ≫
        modFiberStalksLeftUnitor.{u, v} B Λ f s G ≫
          modWeightedTraceStalkMap.{u, v} B Λ f w G s := by
  refine modFiberStalksTensor_hom_ext.{u, v} B Λ f s (𝟙_ _)
    ((modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj G) fun x => ?_
  refine ModuleCat.hom_ext (TensorProduct.ext' fun a g => ?_)
  have hNat := ConcreteCategory.congr_hom
    (modFiberStalkOf_comp_modFiberStalksLeftUnitor.{u, v} B Λ f s G x)
    ((stalkFiberSummandIso.{u, v} B Λ f s (𝟙_ _) G x).hom (a ⊗ₜ g))
  have hSFS := ConcreteCategory.congr_hom
    (stalkFiberSummandIso_comp_map_leftUnitor.{u, v} B Λ f s G x) (a ⊗ₜ g)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hNat hSFS ⊢
  rw [modFiberStalksTensorIso_inv_modFiberStalksTensorOf,
    modFiberStalksSummandsIso_hom_modFiberStalksTensorOf, hNat, hSFS,
    modWeightedTraceStalkMap_modFiberStalkOf, modWeightedTraceStalkSummand_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply,
    ModuleCat.MonoidalCategory.leftUnitor_hom_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply,
    ModuleCat.MonoidalCategory.leftUnitor_hom_apply,
    modUnitWeightedSum_comp_εIso_inv_modFiberStalkOf, smul_assoc]
  simp

/-- **Stacks 0GKG.** The trace `f_!(f^{-1}G) ⟶ G` built from a trace `Tr : f_!(𝟙_) ⟶ 𝟙_` on the
constant sheaf by tensoring with `G` and transporting along the projection formula has the
weighted trace stalks of [Stacks, Tag 0GKG], as soon as `Tr` has them: at every geometric point
`ȳ` of `Y`, read through the decomposition of the stalk of `f_!(f^{-1}G)` into the direct sum of
the stalks of `f^{-1}G` over the geometric fibre above `ȳ`, the trace is the weighted sum over
that fibre. -/
public theorem modHasWeightedTraceStalks_modWeightedTrace (w : X.obj → ℤ)
    (Tr : (fShriekMod.{u, v, max (u + 1) v} B Λ f).obj (𝟙_ _) ⟶ 𝟙_ _)
    (hTr : ModHasUnitTraceStalks.{u, v} B Λ f w Tr)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) :
    ModHasWeightedTraceStalks.{u, v} B Λ f w G (modWeightedTrace.{u, v} B Λ f Tr G) := by
  intro s
  have hTr' : (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).map Tr =
      (modShriekFiberStalksIso.{u, v} B Λ f s (𝟙_ _)).hom ≫
        modUnitWeightedSum.{u, v} B Λ f w s :=
    (Iso.inv_comp_eq (modShriekFiberStalksIso.{u, v} B Λ f s (𝟙_ _))).1 (hTr s)
  have hD1 := (reassoc_of% (modStalkFunctor_μ_comp_modShriekUnitTensorIso.{u, v} B Λ f s G))
    (modWeightedTraceStalkMap.{u, v} B Λ f w G s)
  have hD4 := congrArg (fun m =>
      (modFiberStalksTensorIso.{u, v} B Λ f s (𝟙_ _)
        ((modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj G)).hom ≫ m)
    (modFiberStalksTensorIso_inv_comp_modUnitWeightedSum.{u, v} B Λ f w G s)
  simp only [Iso.hom_inv_id_assoc] at hD4
  have hD : (((modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).map Tr ≫
            (Functor.Monoidal.εIso
              (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s)).inv) ▷
          (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj G) ≫
        (λ_ ((modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj G)).hom =
      Functor.LaxMonoidal.μ (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s)
          ((fShriekMod.{u, v, max (u + 1) v} B Λ f).obj (𝟙_ _)) G ≫
        (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).map
            (modShriekUnitTensorIso.{u, v} B Λ f G).hom ≫
          (modShriekFiberStalksIso.{u, v} B Λ f s
              ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G)).hom ≫
            modWeightedTraceStalkMap.{u, v} B Λ f w G s := by
    rw [hD1, hTr', Category.assoc, comp_whiskerRight, Category.assoc, hD4, tensorHom_id]
  change (modShriekFiberStalksIso.{u, v} B Λ f s
        ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G)).inv ≫
      (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).map
        (modWeightedTrace.{u, v} B Λ f Tr G) =
    modWeightedTraceStalkMap.{u, v} B Λ f w G s
  rw [modStalkFunctor_map_modWeightedTrace, hD, ← Functor.Monoidal.μIso_hom,
    Iso.inv_hom_id_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_assoc]

end AlgebraicGeometry.SmallEtale

end
