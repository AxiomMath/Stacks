module

public import StacksFrontier.AlgebraicGeometry.SectionsColimit.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiQuasicoherentSheaf

/-!
# The canonical map on sections of a pullback, and extension of scalars

For a morphism of schemes `h : X ⟶ S` and a module `F` on `S`, the unit of the
pullback-pushforward adjunction gives a canonical map `Γ(S, F) ⟶ Γ(X, h⁺F)`; this is the map of
the presheaf of Tag 03DS along the arrow of `CategoryTheory.Over S` from `X` to the terminal
object.  This file identifies it, over an affine base and for a quasi-coherent module, with the
unit `m ↦ 1 ⊗ₜ m` of extension of scalars, and records the compatibility of these maps with
composition.

These are the two statements about the presheaf of Tag 03DS that the affine half of Tag 03DT
needs: that half is the exactness of `Γ(F, ⊤) → T ⊗[R] Γ(F, ⊤) ⇉ (T ⊗[R] T) ⊗[R] Γ(F, ⊤)` for a
faithfully flat `R ⟶ T`, whose algebraic input is Stacks 023M
(`Stacks.Descent.exact_mk_rTensor_includeLeftSubRight`), and the geometric input is the
identification of the presheaf maps with the algebraic ones.

## Main definitions

* `Stacks.Sites.sectionsPullbackMap` is the canonical map `Γ(F, ⊤) ⟶ Γ(h⁺F, ⊤)` on global
  sections, for an arbitrary morphism of schemes `h`.
* `Stacks.Sites.specSectionsMap` is the same map for `h = Spec.map φ`, as a morphism of modules
  over the source ring: the target carries the module structure of
  `Stacks.AlgebraicGeometry.SectionsColimit.pullbackSections`.
* `Stacks.Sites.specOver` is the spectrum of a ring, as a scheme over the spectrum of another,
  and `Stacks.Sites.specOverMap` is the morphism of such induced by a factorisation of ring maps.

## Main results

* `Stacks.Sites.sectionsPullbackIso_specSectionsMap`: **the canonical map on sections is the unit
  of extension of scalars.**  For a quasi-coherent module `F` on `Spec R` and a ring map
  `φ : R ⟶ T`, the canonical map `Γ(F, ⊤) ⟶ Γ((Spec.map φ)⁺F, ⊤)` becomes `m ↦ 1 ⊗ₜ m` under
  `Stacks.AlgebraicGeometry.SectionsColimit.sectionsPullbackIso`, the identification of the
  sections of the pullback with `T ⊗[R] Γ(F, ⊤)`.
* `Stacks.Sites.pullbackSectionsMap_sectionsPullbackMap`: **the map of the presheaf of Tag 03DS
  takes the canonical map on sections to the canonical map on sections.**
* `Stacks.Sites.topUnitMap_topUnitMap`: the maps on global sections attached to two composable
  morphisms of schemes compose, with the comparison of the iterated pullback with the pullback
  along the composite inserted.  `Stacks.Sites.unit_app_pullbackComp_inv` is the underlying
  statement about the units themselves.

## Implementation notes

`Stacks.Sites.sectionsPullbackIso_specSectionsMap` is proved from
`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app`:
`Stacks.AlgebraicGeometry.SectionsColimit.tildePullbackIso` is defined as the comparison of two
left adjoints of the sections functor, so it is characterised by its effect on the units, and the
unit of `ModuleCat.extendRestrictScalarsAdj` is `m ↦ 1 ⊗ₜ m`.  Every step is taken on *elements*
rather than on morphisms: `Γ((Scheme.Modules.pushforward j).obj N, ⊤)` and `Γ(N, ⊤)` are the same
type but not the same expression, so a composite in which that identification is implicit is not
matched by `rw`, while `exact` and `congrArg` check it at default transparency.

Two spellings of the same morphism must be kept apart for a cost reason, and the measurement is
sharp.  `AlgebraicGeometry.pullbackSectionsMap_eq_topUnitMap` instantiated at
`Stacks.Sites.specOverMap` is free (2.3 s) when its type is left inferred or written in the
*projection* spelling `(specOverMap ψ α χ h).left`, `(specOver ψ).hom`, and **kernel-times-out**
(over 49 s) when the same statement is written with `Spec.map α`, `Spec.map ψ` in those positions:
the two differ by one `Over.mk`/`Over.homMk` projection, but the comparison happens inside the
type of `Stacks.Sites.pullbackCompIso`, where it descends into the pullback functors of schemes.
Statements about `Stacks.Sites.sectionsPullbackMap` alone are free in either spelling, the
identification there being one `Scheme.Modules.pullback` deep.

## References

* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped AlgebraicGeometry TensorProduct ChangeOfRings
open Scheme.Modules

universe u

namespace Stacks.Sites

open Stacks.AlgebraicGeometry.SectionsColimit

section Sections

variable {R T : CommRingCat.{u}} (φ : R ⟶ T)

/-- The canonical map on global sections induced by pullback along `Spec.map φ`. -/
noncomputable def specSectionsMap (F : (Spec R).Modules) :
    moduleSpecΓFunctor.obj F ⟶
      (pullbackSections φ).obj ((pullback (Spec.map φ)).obj F) :=
  moduleSpecΓFunctor.map ((pullbackPushforwardAdjunction (Spec.map φ)).unit.app F)

/-- `Stacks.Sites.specSectionsMap` is the map on global sections of
`Stacks.Sites.topUnitMap` at the identity comparison. -/
lemma specSectionsMap_apply (F : (Spec R).Modules) (m : ToType Γ(F, ⊤)) :
    specSectionsMap φ F m = topUnitMap (Spec.map φ) (𝟙 ((pullback (Spec.map φ)).obj F)) m :=
  rfl

/-- Global sections of a direct image along `Spec.map φ` are global sections: the map induced by
a morphism of modules on `Spec T` is the same function read on either side. -/
lemma moduleSpecΓFunctor_map_pushforward_apply {N N' : (Spec T).Modules} (h : N ⟶ N')
    (y : ToType (moduleSpecΓFunctor.obj ((pushforward (Spec.map φ)).obj N))) :
    moduleSpecΓFunctor.map ((pushforward (Spec.map φ)).map h) y =
      moduleSpecΓFunctor.map h y := rfl

/-- The canonical map on global sections is natural in the module. -/
lemma specSectionsMap_naturality {F F' : (Spec R).Modules} (ν : F ⟶ F')
    (m : ToType (moduleSpecΓFunctor.obj F)) :
    specSectionsMap φ F' (moduleSpecΓFunctor.map ν m) =
      moduleSpecΓFunctor.map ((pullback (Spec.map φ)).map ν) (specSectionsMap φ F m) := by
  have h2 := congrArg moduleSpecΓFunctor.map
    ((pullbackPushforwardAdjunction (Spec.map φ)).unit.naturality ν)
  rw [Functor.map_comp, Functor.map_comp] at h2
  have h3 := ConcreteCategory.congr_hom h2 m
  simp only [ConcreteCategory.comp_apply, Functor.comp_map, Functor.id_map] at h3
  rwa [moduleSpecΓFunctor_map_pushforward_apply] at h3

/-- For a quasi-coherent module `F` on `Spec R`, the inverse of
`AlgebraicGeometry.Scheme.Modules.fromTildeΓ` acts on global sections as the unit of the
tilde-Gamma adjunction. -/
lemma moduleSpecΓFunctor_map_fromTildeΓ_inv_apply (F : (Spec R).Modules) [F.IsQuasicoherent]
    (m : ToType (moduleSpecΓFunctor.obj F)) :
    moduleSpecΓFunctor.map (asIso (fromTildeΓ F)).inv m =
      tilde.adjunction.unit.app (moduleSpecΓFunctor.obj F) m := by
  refine (ConcreteCategory.bijective_of_isIso
    (moduleSpecΓFunctor.map (fromTildeΓ F))).1 ?_
  have h1 : moduleSpecΓFunctor.map (asIso (fromTildeΓ F)).inv ≫
      moduleSpecΓFunctor.map (fromTildeΓ F) = 𝟙 _ :=
    (moduleSpecΓFunctor.mapIso (asIso (fromTildeΓ F))).inv_hom_id
  exact (ConcreteCategory.congr_hom h1 m).trans
    (ConcreteCategory.congr_hom (tilde.adjunction.right_triangle_components (Y := F)) m).symm

/-- The canonical map on sections of the pullback along `Spec.map φ` of `M^~` is, under the
identification of those sections with `T ⊗[R] M`, the map `m ↦ 1 ⊗ₜ m`. -/
theorem tildeSectionsPullbackIso_specSectionsMap (M : ModuleCat.{u} R) (m : ToType M) :
    (tildeSectionsPullbackIso φ M).hom
        (specSectionsMap φ ((tilde.functor R).obj M) ((tilde.adjunction.unit.app M) m)) =
      (1 : T) ⊗ₜ[(R : Type u), φ.hom] m := by
  have h : (tildePullbackAdjunction φ).unit.app M ≫
      (pullbackSections φ).map ((tildePullbackIso φ).hom.app M) =
      (extendScalarsTildeAdjunction φ).unit.app M :=
    Adjunction.unit_leftAdjointUniq_hom_app _ _ M
  have h1 : (tildePullbackAdjunction φ).unit.app M =
      tilde.adjunction.unit.app M ≫ specSectionsMap φ ((tilde.functor R).obj M) :=
    Adjunction.comp_unit_app _ _ _
  have h3 : (extendScalarsTildeAdjunction φ).unit.app M m =
      tilde.adjunction.unit.app ((ModuleCat.extendScalars φ.hom).obj M)
        ((1 : T) ⊗ₜ[(R : Type u), φ.hom] m) := rfl
  have he := ConcreteCategory.congr_hom h m
  rw [h1, h3] at he
  simp only [ConcreteCategory.comp_apply] at he
  have hts : ∀ z, (tildeSectionsPullbackIso φ M).hom z =
      (tilde.toTildeΓNatIso.app ((ModuleCat.extendScalars φ.hom).obj M)).inv
        (moduleSpecΓFunctor.map ((tildePullbackIso φ).hom.app M) z) := fun _ => rfl
  exact (hts _).trans ((congrArg (ConcreteCategory.hom
      (tilde.toTildeΓNatIso.app ((ModuleCat.extendScalars φ.hom).obj M)).inv) he).trans
    (ConcreteCategory.congr_hom
      (tilde.toTildeΓNatIso.app ((ModuleCat.extendScalars φ.hom).obj M)).hom_inv_id _))

/-- **The canonical map on sections is the unit of extension of scalars.**  For a quasi-coherent
module `F` on `Spec R`, the canonical map from the global sections of `F` to those of its pullback
along `Spec.map φ` is, under the identification of the latter with `T ⊗[R] Γ(F, ⊤)`, the map
`m ↦ 1 ⊗ₜ m`. -/
theorem sectionsPullbackIso_specSectionsMap (F : (Spec R).Modules) [F.IsQuasicoherent]
    (m : ToType (moduleSpecΓFunctor.obj F)) :
    (sectionsPullbackIso φ F).hom (specSectionsMap φ F m) =
      (1 : T) ⊗ₜ[(R : Type u), φ.hom] m := by
  have hsp : ∀ z, (sectionsPullbackIso φ F).hom z =
      (tildeSectionsPullbackIso φ (moduleSpecΓFunctor.obj F)).hom
        (moduleSpecΓFunctor.map ((pullback (Spec.map φ)).map
          (asIso (fromTildeΓ F)).inv) z) := fun _ => rfl
  refine (hsp _).trans ?_
  rw [← specSectionsMap_naturality, moduleSpecΓFunctor_map_fromTildeΓ_inv_apply]
  exact tildeSectionsPullbackIso_specSectionsMap φ (moduleSpecΓFunctor.obj F) m

end Sections

section Composition

variable {T₀ T₁ T₂ : Scheme.{u}}

/-- The unit of the pullback-pushforward adjunction along a composite of morphisms of schemes. -/
lemma unit_app_pullbackComp_inv (f : T₀ ⟶ T₁) (g : T₁ ⟶ T₂) (M : T₂.Modules) :
    (pullbackPushforwardAdjunction (f ≫ g)).unit.app M ≫
      (pushforward (f ≫ g)).map ((pullbackComp f g).inv.app M) =
      (pullbackPushforwardAdjunction g).unit.app M ≫
        (pushforward g).map ((pullbackPushforwardAdjunction f).unit.app
          ((pullback g).obj M)) ≫
        (pushforwardComp f g).hom.app ((pullback f).obj ((pullback g).obj M)) := by
  have h := CategoryTheory.unit_conjugateEquiv
    ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
    (pullbackPushforwardAdjunction (f ≫ g))
    (pullbackComp f g).inv M
  simpa [Adjunction.comp_unit_app, conjugateEquiv_pullbackComp_inv] using h.symm

/-- **The maps on global sections attached to two composable morphisms of schemes compose.** -/
lemma topUnitMap_topUnitMap (f : T₀ ⟶ T₁) (g : T₁ ⟶ T₂) (M : T₂.Modules) {N : T₁.Modules}
    {P : T₀.Modules} (a : (pullback g).obj M ⟶ N) (b : (pullback f).obj N ⟶ P)
    (x : ToType Γ(M, ⊤)) :
    topUnitMap f b (topUnitMap g a x) =
      topUnitMap (f ≫ g) ((pullbackComp f g).inv.app M ≫ (pullback f).map a ≫ b) x := by
  have hnat : (pullbackPushforwardAdjunction f).unit.app ((pullback g).obj M) ≫
      (pushforward f).map ((pullback f).map a ≫ b) =
      a ≫ (pullbackPushforwardAdjunction f).unit.app N ≫ (pushforward f).map b := by
    have hn := (pullbackPushforwardAdjunction f).unit.naturality a
    simp only [Functor.comp_map, Functor.id_map] at hn
    rw [Functor.map_comp, ← Category.assoc, ← hn, Category.assoc]
  have key : (pullbackPushforwardAdjunction (f ≫ g)).unit.app M ≫
      (pushforward (f ≫ g)).map ((pullbackComp f g).inv.app M ≫ (pullback f).map a ≫ b) =
      ((pullbackPushforwardAdjunction g).unit.app M ≫ (pushforward g).map a) ≫
        (pushforward g).map ((pullbackPushforwardAdjunction f).unit.app N ≫
          (pushforward f).map b) ≫
        (pushforwardComp f g).hom.app P := by
    rw [Functor.map_comp, reassoc_of% (unit_app_pullbackComp_inv f g M), Category.assoc,
      ← (pushforwardComp f g).hom.naturality ((pullback f).map a ≫ b), Functor.comp_map,
      ← Functor.map_comp_assoc, hnat]
    simp only [Functor.map_comp, Category.assoc]
  exact (ConcreteCategory.congr_hom
    (congrArg (fun t => Scheme.Modules.Hom.app t (⊤ : T₂.Opens)) key) x).symm

/-- The canonical map on global sections induced by pullback along a morphism of schemes. -/
noncomputable def sectionsPullbackMap {S X : Scheme.{u}} (h : X ⟶ S) (F : S.Modules) :
    Γ(F, ⊤) ⟶ Γ((pullback h).obj F, ⊤) :=
  topUnitMap h (𝟙 ((pullback h).obj F))

/-- `Stacks.Sites.topUnitMap` along equal morphisms of schemes. -/
lemma topUnitMap_pullbackCongr {j j' : T₀ ⟶ T₁} (h : j = j') (M : T₁.Modules)
    (x : ToType Γ(M, ⊤)) :
    topUnitMap j ((pullbackCongr h).hom.app M) x = topUnitMap j' (𝟙 _) x := by
  subst h
  rw [pullbackCongr_rfl_hom_app]

end Composition

section Over

variable {R T W : CommRingCat.{u}}

/-- The spectrum of `T`, as a scheme over the spectrum of `R`. -/
noncomputable abbrev specOver (ψ : R ⟶ T) : Over (Spec R) := Over.mk (Spec.map ψ)

/-- A ring map factorisation gives a factorisation of the corresponding morphisms of spectra. -/
lemma spec_map_comp_eq (ψ : R ⟶ T) (α : T ⟶ W) (χ : R ⟶ W) (h : ψ ≫ α = χ) :
    Spec.map α ≫ Spec.map ψ = Spec.map χ := by
  subst h
  exact (Spec.map_comp ψ α).symm

/-- The morphism of schemes over `Spec R` induced by a ring map `α : T ⟶ W` whose composite
with `ψ` is `χ`. -/
@[reducible] noncomputable def specOverMap (ψ : R ⟶ T) (α : T ⟶ W) (χ : R ⟶ W)
    (h : ψ ≫ α = χ) :
    specOver χ ⟶ specOver ψ :=
  Over.homMk (Spec.map α) (spec_map_comp_eq ψ α χ h)

/-- The underlying morphism of schemes of `specOverMap ψ α χ h` is `Spec.map α`. -/
@[simp] lemma specOverMap_left (ψ : R ⟶ T) (α : T ⟶ W) (χ : R ⟶ W) (h : ψ ≫ α = χ) :
    (specOverMap ψ α χ h).left = Spec.map α := rfl

/-- **The map of the Tag 03DS presheaf takes the canonical map on sections to the canonical map
on sections.**  Both are the unit of the pullback-pushforward adjunction on global sections, and
this is the compatibility of that unit with composition. -/
lemma pullbackSectionsMap_sectionsPullbackMap {S : Scheme.{u}} (F : S.Modules) {A B : Over S}
    (g : A ⟶ B) (m : ToType Γ(F, ⊤)) :
    pullbackSectionsMap F g (sectionsPullbackMap B.hom F m) = sectionsPullbackMap A.hom F m := by
  have hb : (pullbackComp g.left B.hom).inv.app F ≫
      (pullback g.left).map (𝟙 ((pullback B.hom).obj F)) ≫
        (pullbackCompIso F g.left B.hom A.hom (Over.w g)).hom =
      (pullbackCongr (Over.w g)).hom.app F := by
    simp [pullbackCompIso_hom]
  calc pullbackSectionsMap F g (sectionsPullbackMap B.hom F m)
      = topUnitMap g.left (pullbackCompIso F g.left B.hom A.hom (Over.w g)).hom
          (topUnitMap B.hom (𝟙 ((pullback B.hom).obj F)) m) :=
        ConcreteCategory.congr_hom (pullbackSectionsMap_eq_topUnitMap F g) _
    _ = topUnitMap (g.left ≫ B.hom)
          ((pullbackComp g.left B.hom).inv.app F ≫
            (pullback g.left).map (𝟙 ((pullback B.hom).obj F)) ≫
              (pullbackCompIso F g.left B.hom A.hom (Over.w g)).hom) m :=
        topUnitMap_topUnitMap _ _ F _ _ _
    _ = topUnitMap (g.left ≫ B.hom) ((pullbackCongr (Over.w g)).hom.app F) m := by rw [hb]
    _ = topUnitMap A.hom (𝟙 ((pullback A.hom).obj F)) m :=
        topUnitMap_pullbackCongr (Over.w g) F m

end Over

end Stacks.Sites

end
