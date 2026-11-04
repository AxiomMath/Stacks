module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.PentagonAssembly
public import StacksFrontier.AlgebraicGeometry.Descent.Parasitic.FlatCohomologyBaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.Parasitic.FlatCohomologySmallSiteComparison
public import StacksFrontier.AlgebraicGeometry.Descent.Parasitic.FlatCohomologyEtaleClauseTwo
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SectionsComponentsCocycle

/-!
# The canonical map of [Stacks, Tag 0756] clause (2) is a base-change map

Clause (2) of [Stacks, Tag 0756] asserts that a canonical map
`g^*_{τ,small}(𝒢|_{S_τ}) ⟶ 𝒢|_{U_τ}` is an isomorphism for every flat, locally finitely
presented `g : U → S`.  The canonical map is the base-change map of the commutative square of
ringed sites

```
  (Sch/U)_fppf --- a_U ---> U_τ
       |                     |
     f_big               g_{τ,small}
       v                     v
  (Sch/S)_fppf --- a_S ---> S_τ
```

that is, the adjoint transpose of the restriction map `𝒢|_{S_τ} ⟶ g_*(𝒢|_{U_τ})`, which is
`a_{S,*}` of the unit `𝒢 ⟶ f_{big,*} f_big^* 𝒢` followed by the identification
`a_{S,*} f_{big,*} ≅ g_* a_{U,*}` of the two composite direct images.  The development defines
the map, at `τ = Zar` and at `τ = étale`, by the equivalent formula through the comparison of
inverse images of the square — the unit of `a_U^* ⊣ a_{U,*}`, the comparison
`a_U^* g^* ≅ f_big^* a_S^*`, and `a_{U,*} f_big^*` of the counit of `a_S^* ⊣ a_{S,*}` — and this
file proves that the two descriptions agree.

## Main results

* `Stacks.Mates.homEquiv_counit_eq` and `Stacks.Mates.homEquiv_homEquiv_counit_eq`: **the
  transpose of a mate at a counit is the unit of the other adjunction followed by the
  conjugate.**  For `A : a ⊣ r`, `D : ρ ⊣ Rρ`, a third adjunction `adj₂ : L₂ ⊣ R₂` and
  `α : L₂ ≅ a ⋙ ρ`, the `adj₂`-transpose of `α.hom.app (r.obj G) ≫ ρ.map (A.counit.app G)` is
  `r.map (D.unit.app G)` followed by the conjugate of `α` with respect to `A.comp D` and `adj₂`.
  This is the abstract form of the agreement of the two descriptions of a base-change map.
* `AlgebraicGeometry.BigFppfOver.zariskiClause2Map_eq_homEquiv_symm` and
  `AlgebraicGeometry.BigFppfOver.etaleClause2Map_eq_homEquiv_symm`: **the canonical maps of
  clause (2) are the adjoint transposes of the restriction maps**, at `τ = Zar` and at
  `τ = étale`.
* `AlgebraicGeometry.BigFppfOver.zariskiBaseChangeMap_eq`: at `τ = Zar` the restriction map has a
  second, sectionwise description,
  `AlgebraicGeometry.BigFppfOver.objZariskiRestrictionComparison`, restriction along
  `g^{-1}V ⟶ V`, and its transpose `AlgebraicGeometry.BigFppfOver.zariskiBaseChangeMap` is the
  canonical map followed by the identification of the two spellings of `𝒢|_{X_Zar}`; so clause (2)
  may be stated with either, by `AlgebraicGeometry.BigFppfOver.isIso_zariskiClause2Map_iff`.

## Implementation notes

The direct image `f_{big,*}` is `SheafOfModules.overPullback` along the structure morphism, the
right adjoint of `AlgebraicGeometry.BigFppfOver.objRestrictOverPullbackAdjunction`, whose unit is
the unit of `SheafOfModules.overMapPushforwardAdj` — on sections, restriction along the base
change `U ×_S V ⟶ V`.  The identification of composite direct images is then
`AlgebraicGeometry.BigFppfOver.objRestrictSectionsIso` at `τ = Zar` and
`AlgebraicGeometry.BigFppfOver.etaleBaseChangeMate` at `τ = étale`.

The sectionwise description is proved by comparing sections over each open `V` of `S`: both
sides are restriction along an arrow `(g^{-1}V ↪ X → S) ⟶ (V ↪ S)` of the big fppf site, and
there is at most one such arrow, `AlgebraicGeometry.BigFppfOver.subsingleton_hom_opensObj`.
Restriction to an object and its adjunction with `SheafOfModules.overPullback` are equal to
`SheafOfModules.overMap` and `SheafOfModules.overMapPushforwardAdj` only after a transport along
`AlgebraicGeometry.BigFppfOver.objRestrict_eq_overMap`, so the comparison is first proved for an
arbitrary functor equal to `SheafOfModules.overMap`
(`AlgebraicGeometry.BigFppfOver.objZariskiRestrictionComparison_app_eq_of_eq`), where `subst`
removes the transport.

The ring sheaves of the sites involved are written in more than one way — the structure sheaf
of the big fppf site over `S` and the restriction of the structure sheaf of the whole site to
the object `S`, or its fppf member of the five localized structure sheaves — and these agree
only after unfolding semireducible definitions.  The proofs therefore elaborate each instance of
`Stacks.Mates.homEquiv_homEquiv_counit_eq` on its own and close the two sides of the comparison
with the statement separately, so that the spellings are identified one subterm at a time.

## References

* [Stacks Project, Tag 0756](https://stacks.math.columbia.edu/tag/0756)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe v₁ v₂ v₃ u₁ u₂ u₃ u

namespace Stacks.Mates

variable {𝒜 : Type u₁} {ℬ : Type u₂} {𝒞 : Type u₃}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ] [Category.{v₃} 𝒞]
  {a : 𝒜 ⥤ ℬ} {r : ℬ ⥤ 𝒜} (A : a ⊣ r)
  {ρ : ℬ ⥤ 𝒞} {Rρ : 𝒞 ⥤ ℬ} (D : ρ ⊣ Rρ)
  {L₂ : 𝒜 ⥤ 𝒞} {R₂ : 𝒞 ⥤ 𝒜} (adj₂ : L₂ ⊣ R₂)
  (α : L₂ ≅ a ⋙ ρ)

/-- **The transpose of a mate at a counit.**  Let `A : a ⊣ r` and `D : ρ ⊣ Rρ` be adjunctions,
let `adj₂ : L₂ ⊣ R₂` be a third one, and let `α : L₂ ≅ a ⋙ ρ` be an isomorphism of left
adjoints — of `adj₂` on one side and of `A.comp D` on the other.  Then for every object `G`, the
`adj₂`-transpose of

    `L₂(r G) ⟶ ρ(a(r G)) ⟶ ρ G`,

the component of `α` followed by `ρ` of the counit of `A`, is

    `r G ⟶ r(Rρ(ρ G)) ⟶ R₂(ρ G)`,

`r` of the unit of `D` followed by the conjugate of `α`.

Three adjunctions meet here and only one identity is available between them: the unit relation
`CategoryTheory.unit_conjugateEquiv` for the conjugate, which replaces the `adj₂`-unit followed
by `R₂` of `α` by the unit of `A.comp D` followed by the conjugate.  What is left is naturality
of the conjugate, naturality of the unit of `D`, and the triangle identity of `A` at `G`, which
is where the counit of `A` cancels against the unit of `A` and the composite collapses to the
unit of `D`. -/
public theorem homEquiv_counit_eq (G : ℬ) :
    adj₂.homEquiv (r.obj G) (ρ.obj G)
        (α.hom.app (r.obj G) ≫ ρ.map (A.counit.app G)) =
      r.map (D.unit.app G) ≫ (conjugateIsoEquiv (A.comp D) adj₂ α).hom.app (ρ.obj G) := by
  have hβ : (conjugateIsoEquiv (A.comp D) adj₂ α).hom =
      conjugateEquiv (A.comp D) adj₂ α.hom := rfl
  have hnat : (conjugateEquiv (A.comp D) adj₂ α.hom).app (ρ.obj (a.obj (r.obj G))) ≫
        R₂.map (ρ.map (A.counit.app G)) =
      r.map (Rρ.map (ρ.map (A.counit.app G))) ≫
        (conjugateEquiv (A.comp D) adj₂ α.hom).app (ρ.obj G) :=
    ((conjugateEquiv (A.comp D) adj₂ α.hom).naturality (ρ.map (A.counit.app G))).symm
  have htri : (A.comp D).unit.app (r.obj G) ≫ r.map (Rρ.map (ρ.map (A.counit.app G))) =
      r.map (D.unit.app G) := by
    have hD : D.unit.app (a.obj (r.obj G)) ≫ Rρ.map (ρ.map (A.counit.app G)) =
        A.counit.app G ≫ D.unit.app G := (D.unit.naturality (A.counit.app G)).symm
    rw [Adjunction.comp_unit_app, Category.assoc, ← r.map_comp, hD, r.map_comp,
      ← Category.assoc, A.right_triangle_components]
    exact Category.id_comp _
  rw [Adjunction.homEquiv_apply, Functor.map_comp, ← Category.assoc,
    ← unit_conjugateEquiv (A.comp D) adj₂ α.hom (r.obj G), hβ, Category.assoc]
  show (A.comp D).unit.app (r.obj G) ≫
      (conjugateEquiv (A.comp D) adj₂ α.hom).app (ρ.obj (a.obj (r.obj G))) ≫
        R₂.map (ρ.map (A.counit.app G)) = _
  rw [hnat, ← Category.assoc, htri]

/-- **`Stacks.Mates.homEquiv_counit_eq` with the third adjunction a composite.**  When the third
adjunction is a composite `E.comp X` of `E : e ⊣ eₛ` and `X : x ⊣ rₓ` and the isomorphism of left
adjoints is given as `α : a ⋙ ρ ≅ e ⋙ x`, the transpose is taken in two steps: under `X` and then
under `E`. -/
public theorem homEquiv_homEquiv_counit_eq {𝒟 : Type*} [Category 𝒟] {e : 𝒜 ⥤ 𝒟} {eₛ : 𝒟 ⥤ 𝒜}
    (E : e ⊣ eₛ) {x : 𝒟 ⥤ 𝒞} {rₓ : 𝒞 ⥤ 𝒟} (X : x ⊣ rₓ) (α : a ⋙ ρ ≅ e ⋙ x) (G : ℬ) :
    E.homEquiv (r.obj G) (rₓ.obj (ρ.obj G))
        (X.homEquiv (e.obj (r.obj G)) (ρ.obj G)
          (α.inv.app (r.obj G) ≫ ρ.map (A.counit.app G))) =
      r.map (D.unit.app G) ≫
        (conjugateIsoEquiv (A.comp D) (E.comp X) α.symm).hom.app (ρ.obj G) := by
  rw [← homEquiv_counit_eq A D (E.comp X) α.symm G, Adjunction.comp_homEquiv]
  rfl

end Stacks.Mates

namespace AlgebraicGeometry.BigFppfOver

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (T : BigFppfOver B S hS) (G : SheafOfModules.{u} (structureSheaf B S hS))

/-! ### The canonical map of clause (2) as a transpose -/

/-- **The canonical map of clause (2) of [Stacks, Tag 0756] at `τ = Zar` is a transpose at the
counit.**  `AlgebraicGeometry.BigFppfOver.zariskiClause2Map` is, under the associated-module
adjunction of the big fppf site of the scheme of `T`, the transpose of the component of the
comparison of [Stacks, Tag 03DV] at `𝒢|_{S_Zar}` followed by the restriction to that site of the
counit of the associated-module adjunction of the big fppf site of `S`. -/
public theorem zariskiClause2Map_eq_homEquiv :
    zariskiClause2Map B S hS T G =
      (associatedModuleAdjunction B (objScheme B S hS T)
          (contains_objScheme B S hS T)).homEquiv
        ((Scheme.Modules.pullback (objHom B S hS T)).obj ((restrictModule B S hS).obj G))
        ((objRestrict B S hS T).obj G)
        ((associatedModuleObjRestrictNatIso B S hS T).hom.app
            ((restrictModule B S hS).obj G) ≫
          (objRestrict B S hS T).map ((associatedModuleAdjunction B S hS).counit.app G)) := by
  rw [Adjunction.homEquiv_apply, Functor.map_comp, ← Category.assoc]
  rfl

/-! ### The canonical map of clause (2) is the base-change map of the square of ringed sites -/

/-- **The canonical map of clause (2) of [Stacks, Tag 0756] at `τ = Zar` is the adjoint transpose
of the restriction map `𝒢|_{S_Zar} ⟶ g_*(𝒢|_{X_Zar})`.**  That map is the restriction to `S_Zar`
of the unit `𝒢 ⟶ f_{big,*}(𝒢|_{(Sch/X)_fppf})` of restriction to an object — the unit of
`SheafOfModules.overMapPushforwardAdj`, which on sections over `V` is restriction along the base
change `X ×_S V ⟶ V` — followed by the identification
`AlgebraicGeometry.BigFppfOver.objRestrictSectionsIso` of the two composite direct images, a
composite of comparisons of direct images by
`AlgebraicGeometry.BigFppfOver.objRestrictSectionsIso_eq_explicit` and a restriction along an
arrow of the big fppf site on sections by
`AlgebraicGeometry.BigFppfOver.induced_objRestrictSectionsIso_hom`.  So
`AlgebraicGeometry.BigFppfOver.zariskiClause2Map` is the base-change map of the square formed by
`f_big`, the two restrictions to small Zariski sites and `g`, which is how the source describes
the canonical map. -/
public theorem zariskiClause2Map_eq_homEquiv_symm :
    zariskiClause2Map B S hS T G =
      ((Scheme.Modules.pullbackPushforwardAdjunction (objHom B S hS T)).homEquiv
          ((restrictModule B S hS).obj G) (objZariskiRestrict B S hS T G)).symm
        ((restrictModule B S hS).map ((objRestrictOverPullbackAdjunction B S hS T).unit.app G) ≫
          (objRestrictSectionsIso B S hS T).hom.app ((objRestrict B S hS T).obj G)) := by
  have hkey := Stacks.Mates.homEquiv_homEquiv_counit_eq (associatedModuleAdjunction B S hS)
    (objRestrictOverPullbackAdjunction B S hS T)
    (Scheme.Modules.pullbackPushforwardAdjunction (objHom B S hS T))
    (associatedModuleAdjunction B (objScheme B S hS T) (contains_objScheme B S hS T))
    (associatedModuleObjRestrictNatIso B S hS T).symm G
  rw [Equiv.eq_symm_apply, zariskiClause2Map_eq_homEquiv]
  refine Eq.trans ?_ (Eq.trans hkey ?_)
  · rfl
  · congr 2

/-! ### The sectionwise restriction comparison is the restriction map -/

section Sectionwise

open Stacks.SectionsComponents

private theorem induced_objZariskiRestrictionComparison (Z : S.Opens) :
    Induced G ((objZariskiRestrictionComparison B S hS T).app G) (op Z)
      ((opensToBig B S hS).obj Z) (objPreimageObj B S hS T Z) :=
  ⟨objPreimageHom B S hS T Z, rfl, rfl, fun _ => rfl⟩

private theorem induced_restrictModule_map_unit
    (F : SheafOfModules.{u} (structureSheaf B S hS) ⥤
      SheafOfModules.{u} (structureSheaf B (objScheme B S hS T) (contains_objScheme B S hS T)))
    (hF : F = SheafOfModules.overMap.{u} B.structureSheaf T.hom)
    (D : F ⊣ SheafOfModules.overPullback.{u} B.structureSheaf T.hom)
    (hD : HEq D (SheafOfModules.overMapPushforwardAdj.{u} B.structureSheaf T.hom))
    (Z : S.Opens) :
    Induced G ((restrictModule B S hS).map (D.unit.app G)) (op Z)
      ((opensToBig B S hS).obj Z)
      ((Over.map T.hom).obj ((Over.pullback T.hom).obj ((opensToBig B S hS).obj Z))) := by
  subst hF
  obtain rfl := eq_of_heq hD
  exact ⟨(Over.mapPullbackAdj T.hom).counit.app _, rfl, rfl, fun _ => rfl⟩

private theorem induced_objRestrictSectionsIso_of_eq
    (N : SheafOfModules.{u} (structureSheaf B (objScheme B S hS T) (contains_objScheme B S hS T)))
    (hN : N = (SheafOfModules.overMap.{u} B.structureSheaf T.hom).obj G) (Z : S.Opens) :
    Induced G ((objRestrictSectionsIso B S hS T).hom.app N) (op Z)
      ((Over.map T.hom).obj ((Over.pullback T.hom).obj ((opensToBig B S hS).obj Z)))
      (objPreimageObj B S hS T Z) := by
  subst hN
  obtain ⟨v, e₁, e₂, hv⟩ := induced_objRestrictSectionsIso_hom B S hS T
    ((SheafOfModules.overMap.{u} B.structureSheaf T.hom).obj G) Z
  exact ⟨(Over.map T.hom).map v, e₁, e₂, fun y => (hv y).trans rfl⟩

private theorem induced_pushforward_map_objZariskiRestrictIsoOfEq
    (F : SheafOfModules.{u} (structureSheaf B S hS) ⥤
      SheafOfModules.{u} (structureSheaf B (objScheme B S hS T) (contains_objScheme B S hS T)))
    (hF : F = SheafOfModules.overMap.{u} B.structureSheaf T.hom) (Z : S.Opens) :
    Induced G ((Scheme.Modules.pushforward (objHom B S hS T)).map
        ((objZariskiRestrictIsoOfEq B S hS T F hF).hom.app G)) (op Z)
      (objPreimageObj B S hS T Z) (objPreimageObj B S hS T Z) := by
  subst hF
  exact Induced.ofCast _ _ rfl (fun _ => rfl) rfl

private theorem eq_of_induced_opensToBig {M₂ : S.Modules}
    (f k : (restrictModule B S hS).obj G ⟶ M₂)
    (hf : ∀ Z : S.Opens,
      Induced G f (op Z) ((opensToBig B S hS).obj Z) (objPreimageObj B S hS T Z))
    (hk : ∀ Z : S.Opens,
      Induced G k (op Z) ((opensToBig B S hS).obj Z) (objPreimageObj B S hS T Z)) :
    f = k := by
  ext Z x
  have := subsingleton_hom_opensObj B S hS (objPreimageObj B S hS T Z) Z
  exact induced_eq_app G (hf Z) (hk Z) x

/-- **The sectionwise restriction comparison is the restriction map**, for any spelling of
restriction to an object equal to `SheafOfModules.overMap`.  Let `F` be a functor equal to
`SheafOfModules.overMap` of the structure morphism of `T` and `D` an adjunction
`F ⊣ SheafOfModules.overPullback` heterogeneously equal to `SheafOfModules.overMapPushforwardAdj`.
Then the restriction comparison `𝒢|_{S_Zar} ⟶ g_*(𝒢|_{X_Zar})` along `g^{-1}V ⟶ V` is the
restriction of the unit of `D`, followed by `AlgebraicGeometry.BigFppfOver.objRestrictSectionsIso`
and the identification `AlgebraicGeometry.BigFppfOver.objZariskiRestrictIsoOfEq`.

After `subst` everything is at `SheafOfModules.overMap`, where each of the three factors is, on
sections over an open `V` of `S`, restriction along an arrow of the big fppf site, and the two
sides are restrictions along arrows `(g^{-1}V ↪ X → S) ⟶ (V ↪ S)`, of which there is at most
one by `AlgebraicGeometry.BigFppfOver.subsingleton_hom_opensObj`. -/
public theorem objZariskiRestrictionComparison_app_eq_of_eq
    (F : SheafOfModules.{u} (structureSheaf B S hS) ⥤
      SheafOfModules.{u} (structureSheaf B (objScheme B S hS T) (contains_objScheme B S hS T)))
    (hF : F = SheafOfModules.overMap.{u} B.structureSheaf T.hom)
    (D : F ⊣ SheafOfModules.overPullback.{u} B.structureSheaf T.hom)
    (hD : HEq D (SheafOfModules.overMapPushforwardAdj.{u} B.structureSheaf T.hom)) :
    (objZariskiRestrictionComparison B S hS T).app G =
      ((restrictModule B S hS).map (D.unit.app G) ≫
        (objRestrictSectionsIso B S hS T).hom.app (F.obj G)) ≫
          (Scheme.Modules.pushforward (objHom B S hS T)).map
            ((objZariskiRestrictIsoOfEq B S hS T F hF).hom.app G) :=
  eq_of_induced_opensToBig B S hS T G _ _
    (induced_objZariskiRestrictionComparison B S hS T G)
    (fun Z => ((induced_restrictModule_map_unit B S hS T G F hF D hD Z).comp
      (induced_objRestrictSectionsIso_of_eq B S hS T G (F.obj G)
        (congrArg (fun K => K.obj G) hF) Z)).comp
      (induced_pushforward_map_objZariskiRestrictIsoOfEq B S hS T G F hF Z))

/-- **The sectionwise restriction comparison is the restriction map**: the restriction
comparison `𝒢|_{S_Zar} ⟶ g_*(𝒢|_{X_Zar})` along `g^{-1}V ⟶ V` is the restriction to `S_Zar` of
the unit of `AlgebraicGeometry.BigFppfOver.objRestrictOverPullbackAdjunction`, followed by
`AlgebraicGeometry.BigFppfOver.objRestrictSectionsIso` and the identification
`AlgebraicGeometry.BigFppfOver.objZariskiRestrictIso` of the two spellings of `𝒢|_{X_Zar}`. -/
public theorem objZariskiRestrictionComparison_app_eq :
    (objZariskiRestrictionComparison B S hS T).app G =
      ((restrictModule B S hS).map ((objRestrictOverPullbackAdjunction B S hS T).unit.app G) ≫
        (objRestrictSectionsIso B S hS T).hom.app ((objRestrict B S hS T).obj G)) ≫
          (Scheme.Modules.pushforward (objHom B S hS T)).map
            ((objZariskiRestrictIso B S hS T).hom.app G) := by
  refine (objZariskiRestrictionComparison_app_eq_of_eq B S hS T G (objRestrict B S hS T)
    (objRestrict_eq_overMap B S hS T) (objRestrictOverPullbackAdjunction B S hS T)
    (objRestrictOverPullbackAdjunction_heq B S hS T)).trans ?_
  congr 2

/-- **The sectionwise base-change map is the canonical map of clause (2) of [Stacks, Tag 0756]**
at `τ = Zar`: the adjoint transpose `AlgebraicGeometry.BigFppfOver.zariskiBaseChangeMap` of
restriction along `g^{-1}V ⟶ V` is `AlgebraicGeometry.BigFppfOver.zariskiClause2Map` followed by
the identification `AlgebraicGeometry.BigFppfOver.objZariskiRestrictIso` of the two spellings of
`𝒢|_{X_Zar}`.  This is `AlgebraicGeometry.BigFppfOver.objZariskiRestrictionComparison_app_eq`
transposed, by `AlgebraicGeometry.BigFppfOver.zariskiClause2Map_eq_homEquiv_symm`. -/
public theorem zariskiBaseChangeMap_eq :
    zariskiBaseChangeMap B S hS T G =
      zariskiClause2Map B S hS T G ≫ (objZariskiRestrictIso B S hS T).hom.app G := by
  have hbc : zariskiBaseChangeMap B S hS T G =
      ((Scheme.Modules.pullbackPushforwardAdjunction (objHom B S hS T)).homEquiv
        ((restrictModule B S hS).obj G)
        ((objZariskiPushforward B S hS T).obj G)).symm
          ((objZariskiRestrictionComparison B S hS T).app G) := rfl
  rw [hbc, Equiv.symm_apply_eq, Adjunction.homEquiv_naturality_right,
    objZariskiRestrictionComparison_app_eq, zariskiClause2Map_eq_homEquiv_symm,
    Equiv.apply_symm_apply]

/-- **The canonical map of clause (2) of [Stacks, Tag 0756] at `τ = Zar` is an isomorphism exactly
when its sectionwise transpose is.** -/
public theorem isIso_zariskiClause2Map_iff :
    IsIso (zariskiClause2Map B S hS T G) ↔ IsIso (zariskiBaseChangeMap B S hS T G) := by
  rw [zariskiBaseChangeMap_eq]
  exact ⟨fun _ => inferInstance, fun _ => IsIso.of_isIso_comp_right _
    ((objZariskiRestrictIso B S hS T).hom.app G)⟩

end Sectionwise

/-- **The identification of the two composite direct images of the square of ringed sites at
`τ = étale`.**  For `f : X ⟶ S` the structure morphism of an object `T` of `(Sch/S)_fppf`, this is

    `a_{S,*} ∘ f_{big,*}  ≅  ε_{f,*} ∘ a_{X,*}`,

the mate of the comparison of inverse images
`AlgebraicGeometry.BigFppfOver.smallEtaleToBaseObjRestrictNatIso`, the direct image `f_{big,*}`
being the base change `SheafOfModules.overPullback` along `f` of
`AlgebraicGeometry.BigFppfOver.objRestrictOverPullbackAdjunction`.  It is the étale counterpart of
`AlgebraicGeometry.BigFppfOver.objRestrictSectionsIso`. -/
public abbrev etaleBaseChangeMate :=
  conjugateIsoEquiv ((smallEtaleToBaseModuleAdjunction B S hS .fppf).comp
      (objRestrictOverPullbackAdjunction B S hS T))
    ((objSmallEtaleAdjunction B S hS T).comp
      (smallEtaleToBaseModuleAdjunction B (objScheme B S hS T) (contains_objScheme B S hS T)
        .fppf))
    (smallEtaleToBaseObjRestrictNatIso B S hS T).symm

/-- **The canonical map of clause (2) at `τ = étale` is a transpose at the counit**, under the
adjunction `a_X^* ⊣ a_{X,*}`: of the comparison of inverse images
`AlgebraicGeometry.BigFppfOver.smallEtaleToBaseObjRestrictNatIso` at `𝒢|_{S_étale}` followed by
the restriction of the counit of `a_S^* ⊣ a_{S,*}` at `𝒢`. -/
public theorem etaleClause2Map_eq_homEquiv :
    etaleClause2Map B S hS T G =
      (smallEtaleToBaseModuleAdjunction B (objScheme B S hS T)
          (contains_objScheme B S hS T) .fppf).homEquiv
        ((objSmallEtalePullback B S hS T).obj
          ((smallEtaleToBasePushforward B S hS .fppf).obj G))
        ((objRestrict B S hS T).obj G)
        ((smallEtaleToBaseObjRestrictNatIso B S hS T).inv.app
            ((smallEtaleToBasePushforward B S hS .fppf).obj G) ≫
          (objRestrict B S hS T).map
            ((smallEtaleToBaseModuleAdjunction B S hS .fppf).counit.app G)) := by
  refine Eq.trans ?_ (Adjunction.homEquiv_unit _ _ _ _).symm
  exact Eq.trans (Category.assoc _ _ _) (congrArg _ (Functor.map_comp _ _ _).symm)

/-- **The canonical map of clause (2) of [Stacks, Tag 0756] at `τ = étale` is the adjoint
transpose of the restriction map `𝒢|_{S_étale} ⟶ ε_{f,*}(𝒢|_{X_étale})`.**  That map is the
restriction to `S_étale` of the unit `𝒢 ⟶ f_{big,*}(𝒢|_{(Sch/X)_fppf})` of restriction to an
object — on sections over an étale `W ⟶ S`, restriction along the base change `X ×_S W ⟶ W` —
followed by the identification `AlgebraicGeometry.BigFppfOver.etaleBaseChangeMate` of the two
composite direct images.  So `AlgebraicGeometry.BigFppfOver.etaleClause2Map` is the base-change
map of the square formed by `f_big`, `a_S`, `a_X` and `ε_f`, which is how the source describes
the canonical map. -/
public theorem etaleClause2Map_eq_homEquiv_symm :
    etaleClause2Map B S hS T G =
      ((objSmallEtaleAdjunction B S hS T).homEquiv
          ((smallEtaleToBasePushforward B S hS .fppf).obj G)
          (objSmallEtaleRestrict B S hS T G)).symm
        ((smallEtaleToBasePushforward B S hS .fppf).map
            ((objRestrictOverPullbackAdjunction B S hS T).unit.app G) ≫
          (etaleBaseChangeMate B S hS T).hom.app ((objRestrict B S hS T).obj G)) := by
  have hkey := Stacks.Mates.homEquiv_homEquiv_counit_eq
    (smallEtaleToBaseModuleAdjunction B S hS .fppf) (objRestrictOverPullbackAdjunction B S hS T)
    (objSmallEtaleAdjunction B S hS T)
    (smallEtaleToBaseModuleAdjunction B (objScheme B S hS T) (contains_objScheme B S hS T) .fppf)
    (smallEtaleToBaseObjRestrictNatIso B S hS T) G
  rw [Equiv.eq_symm_apply, etaleClause2Map_eq_homEquiv]
  refine Eq.trans ?_ (Eq.trans hkey ?_)
  · rfl
  · congr 2

end AlgebraicGeometry.BigFppfOver

end
