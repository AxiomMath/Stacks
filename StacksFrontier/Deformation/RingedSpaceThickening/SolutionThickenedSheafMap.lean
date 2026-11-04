module

public import StacksFrontier.Deformation.RingedSpaceThickening.SolutionLiftTargetIso

/-!
# The map of thickened structure sheaves induced by a morphism of deformed spaces

Let `Q₁` and `Q₂` be solutions of deformation problems of **Stacks 08U7** for the same
`f : X ⟶ S` over two first order thickenings `S ⊂ S'₁` and `S ⊂ S'₂` of the base, and let
`φ : X'₂ ⟶ X'₁` be a morphism of the deformed spaces under `X`. Reading `𝒪_{X'₁}` and `𝒪_{X'₂}` on
the opens of `X` through the homeomorphisms of the thickenings, the comorphism of `φ` is a map
`𝒪_{X'₁} ⟶ 𝒪_{X'₂}` of sheaves of rings on `X`, compatible with the two reductions to `𝒪_X`.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.DeformationSolution.thickenedSheafMap`: the map
  `𝒪_{X'₁} ⟶ 𝒪_{X'₂}` on the opens of `X`.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.DeformationSolution.thickenedSheafMap_comp_reduction`:
  it is compatible with the reductions.
* `AlgebraicGeometry.RingedSpaceThickening.DeformationSolution.thickenedSheafMap_app_c_app`: on
  the comorphism of a morphism `p : X'₁ ⟶ T` it is the comorphism of `φ ≫ p`.

## References

* [Stacks Project, Tag 08U7](https://stacks.math.columbia.edu/tag/08U7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.RingedSpaceThickening.DeformationSolution

/-- Three restriction maps of a presheaf on the opens of a space are one restriction map. -/
theorem presheaf_map_map_map_apply {T : TopCat.{u}} (F : (Opens T)ᵒᵖ ⥤ CommRingCat.{u})
    {A B C D : (Opens T)ᵒᵖ} (c : A ⟶ B) (b : B ⟶ C) (a : C ⟶ D) (d : A ⟶ D) (y : F.obj A) :
    (F.map a).hom ((F.map b).hom ((F.map c).hom y)) = (F.map d).hom y := by
  rw [Subsingleton.elim d (c ≫ b ≫ a), F.map_comp, F.map_comp]
  rfl

/-- Two restriction maps of a presheaf on the opens of a space are one restriction map. -/
theorem presheaf_map_map_apply {T : TopCat.{u}} (F : (Opens T)ᵒᵖ ⥤ CommRingCat.{u})
    {A B C : (Opens T)ᵒᵖ} (b : A ⟶ B) (a : B ⟶ C) (d : A ⟶ C) (y : F.obj A) :
    (F.map a).hom ((F.map b).hom y) = (F.map d).hom y := by
  rw [Subsingleton.elim d (b ≫ a), F.map_comp]
  rfl

variable {X S S'₁ S'₂ : RingedSpace.{u, u}} {t₁ : S ⟶ S'₁} {ht₁ : IsFirstOrderThickening t₁}
  {t₂ : S ⟶ S'₂} {ht₂ : IsFirstOrderThickening t₂} {f : X ⟶ S}
  {G₁ G₂ : SheafOfModules.{u} (structureSheafRing X)}
  {c₁ : (modulePullback f).obj
    ((modulePullback t₁).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t₁)) ⟶ G₁}
  {c₂ : (modulePullback f).obj
    ((modulePullback t₂).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t₂)) ⟶ G₂}
  (Q₁ : DeformationSolution t₁ ht₁ f G₁ c₁) (Q₂ : DeformationSolution t₂ ht₂ f G₂ c₂)
  (φ : Q₂.X' ⟶ Q₁.X') (hφ : Q₂.i ≫ φ = Q₁.i)

include hφ in
/-- The map `X ⟶ X'₂ ⟶ X'₁` read through the inverse homeomorphisms. -/
theorem base_comp_baseIso_inv : φ.hom.base ≫ Q₁.baseIso.inv = Q₂.baseIso.inv := by
  have hb : Q₂.baseIso.hom ≫ φ.hom.base = Q₁.baseIso.hom :=
    congrArg (fun m : X ⟶ Q₁.X' => m.hom.base) hφ
  rw [Iso.comp_inv_eq, ← hb, Iso.inv_hom_id_assoc]

include hφ in
/-- The open of `X'₂` over the open of `X'₁` matching an open of `X` is the open of `X'₂`
matching it. -/
theorem opens_map_thickenedSheafMap (U : Opens X.carrier) :
    (Opens.map φ.hom.base).obj ((Opens.map Q₁.baseIso.inv).obj U) =
      (Opens.map Q₂.baseIso.inv).obj U := by
  rw [← Opens.map_comp_obj, Q₁.base_comp_baseIso_inv Q₂ φ hφ]

include hφ in
/-- `opens_map_thickenedSheafMap` on the opposite category. -/
theorem opens_map_thickenedSheafMap_op (U : (Opens X.carrier)ᵒᵖ) :
    (Opens.map φ.hom.base).op.obj ((Opens.map Q₁.baseIso.inv).op.obj U) =
      (Opens.map Q₂.baseIso.inv).op.obj U :=
  congrArg op (Q₁.opens_map_thickenedSheafMap Q₂ φ hφ U.unop)

/-- **The comorphism of `φ : X'₂ ⟶ X'₁`, read on the opens of `X`.** -/
def thickenedPresheafMap : Q₁.thickenedPresheaf ⟶ Q₂.thickenedPresheaf where
  app U := φ.hom.c.app ((Opens.map Q₁.baseIso.inv).op.obj U) ≫
    Q₂.X'.presheaf.map (eqToHom (Q₁.opens_map_thickenedSheafMap_op Q₂ φ hφ U))
  naturality {U V} k := by
    have hnat := φ.hom.c.naturality ((Opens.map Q₁.baseIso.inv).op.map k)
    simp only [TopCat.Presheaf.pushforward_obj_map, Functor.comp_map] at hnat ⊢
    rw [reassoc_of% hnat]
    simp only [Category.assoc, ← Functor.map_comp]
    exact congrArg (fun m => φ.hom.c.app _ ≫ Q₂.X'.presheaf.map m) (Subsingleton.elim _ _)

/-- **The map `𝒪_{X'₁} ⟶ 𝒪_{X'₂}` of sheaves of rings on `X`** given by `φ : X'₂ ⟶ X'₁`. -/
abbrev thickenedSheafMap : Q₁.thickenedSheaf ⟶ Q₂.thickenedSheaf :=
  ObjectProperty.homMk (Q₁.thickenedPresheafMap Q₂ φ hφ)

/-- On an open `U` of `X`, `thickenedSheafMap` is the comorphism of `φ` on the open of `X'₁`
matching `U`, followed by restriction to the open of `X'₂` matching `U`. -/
theorem thickenedSheafMap_app (U : (Opens X.carrier)ᵒᵖ) :
    (Q₁.thickenedSheafMap Q₂ φ hφ).hom.app U =
      φ.hom.c.app ((Opens.map Q₁.baseIso.inv).op.obj U) ≫
        Q₂.X'.presheaf.map (eqToHom (Q₁.opens_map_thickenedSheafMap_op Q₂ φ hφ U)) :=
  rfl

/-- **The map of thickened structure sheaves is compatible with the reductions.** -/
theorem thickenedSheafMap_comp_reduction :
    Q₁.thickenedSheafMap Q₂ φ hφ ≫ Q₂.thickenedSheafReduction = Q₁.thickenedSheafReduction := by
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun U =>
    CommRingCat.hom_ext (RingHom.ext fun x => ?_)))
  have hc := congrArg (fun m => m.hom x) (PresheafedSpace.congr_app
    (congrArg (fun m : X ⟶ Q₁.X' => m.hom) hφ) ((Opens.map Q₁.baseIso.inv).op.obj U))
  have hnat := congrArg (fun m => m.hom ((φ.hom.c.app ((Opens.map Q₁.baseIso.inv).op.obj U)).hom x))
    (Q₂.i.hom.c.naturality (eqToHom (Q₁.opens_map_thickenedSheafMap_op Q₂ φ hφ U)))
  simp only [TopCat.Presheaf.pushforward_obj_map] at hnat hc
  change (Q₂.thickenedReduction.app U).hom ((Q₂.X'.presheaf.map _).hom
    ((φ.hom.c.app ((Opens.map Q₁.baseIso.inv).op.obj U)).hom x)) =
      (Q₁.thickenedReduction.app U).hom x
  rw [thickenedReduction_app]
  refine Eq.trans ?_ (Q₁.thickenedReduction_app U x).symm
  have h4 : (Q₂.i.hom.c.app ((Opens.map Q₂.baseIso.inv).op.obj U)).hom ((Q₂.X'.presheaf.map
      (eqToHom (Q₁.opens_map_thickenedSheafMap_op Q₂ φ hφ U))).hom
        ((φ.hom.c.app ((Opens.map Q₁.baseIso.inv).op.obj U)).hom x)) =
      (X.presheaf.map ((Opens.map Q₂.i.hom.base).op.map
        (eqToHom (Q₁.opens_map_thickenedSheafMap_op Q₂ φ hφ U)))).hom
        (((Q₂.i ≫ φ).hom.c.app ((Opens.map Q₁.baseIso.inv).op.obj U)).hom x) := hnat
  have h5 : ((Q₂.i ≫ φ).hom.c.app ((Opens.map Q₁.baseIso.inv).op.obj U)).hom x =
      (X.presheaf.map (eqToHom (by rw [hφ]))).hom
        ((Q₁.i.hom.c.app ((Opens.map Q₁.baseIso.inv).op.obj U)).hom x) := hc
  refine (congrArg (X.presheaf.map (Q₂.roundTripHom U)).hom (h4.trans
    (congrArg (X.presheaf.map _).hom h5))).trans ?_
  exact presheaf_map_map_map_apply X.presheaf _ _ _ _ _

/-- **The map of thickened structure sheaves on a comorphism.** For `p : X'₁ ⟶ T` and an open `V`
of `T` whose preimage in `X'₁` is the open matching an open `W` of `X`, the map carries the
comorphism of `p` on a section `s` to the comorphism of `φ ≫ p`. -/
theorem thickenedSheafMap_app_c_app {T : RingedSpace.{u, u}} (p : Q₁.X' ⟶ T)
    (V : Opens T.carrier) (W : Opens X.carrier)
    (hW₁ : (Opens.map p.hom.base).obj V = (Opens.map Q₁.baseIso.inv).obj W)
    (hW₂ : (Opens.map (φ ≫ p).hom.base).obj V = (Opens.map Q₂.baseIso.inv).obj W)
    (s : T.presheaf.obj (op V)) :
    ((Q₁.thickenedSheafMap Q₂ φ hφ).hom.app (op W)).hom
        ((Q₁.X'.presheaf.map (eqToHom (congrArg op hW₁))).hom ((p.hom.c.app (op V)).hom s)) =
      (Q₂.X'.presheaf.map (eqToHom (congrArg op hW₂))).hom (((φ ≫ p).hom.c.app (op V)).hom s) := by
  have hnat := congrArg (fun m => m.hom ((p.hom.c.app (op V)).hom s))
    (φ.hom.c.naturality (eqToHom (congrArg op hW₁)))
  simp only [TopCat.Presheaf.pushforward_obj_map] at hnat
  rw [thickenedSheafMap_app]
  change (Q₂.X'.presheaf.map _).hom ((φ.hom.c.app _).hom ((Q₁.X'.presheaf.map _).hom _)) = _
  have h2 : (φ.hom.c.app (op ((Opens.map Q₁.baseIso.inv).obj W))).hom
      ((Q₁.X'.presheaf.map (eqToHom (congrArg op hW₁))).hom ((p.hom.c.app (op V)).hom s)) =
      (Q₂.X'.presheaf.map ((Opens.map φ.hom.base).op.map (eqToHom (congrArg op hW₁)))).hom
        ((φ.hom.c.app (op ((Opens.map p.hom.base).obj V))).hom ((p.hom.c.app (op V)).hom s)) :=
    hnat
  refine (congrArg (Q₂.X'.presheaf.map _).hom h2).trans ?_
  exact presheaf_map_map_apply Q₂.X'.presheaf _ _ _ _

include hφ in
/-- The two maps `|X| ⟶ |T|` through `X'₁` and through `X'₂ ⟶ X'₁` agree. -/
theorem base_comp_eq {T : RingedSpace.{u, u}} (p : Q₁.X' ⟶ T) :
    Q₁.i.hom.base ≫ p.hom.base = Q₂.i.hom.base ≫ (φ ≫ p).hom.base := by
  rw [← hφ]
  rfl

/-- **The algebra structure given by `p : X'₁ ⟶ T`, followed by the map of thickened structure
sheaves, is the algebra structure given by `φ ≫ p`.** -/
theorem comorphismOnOpens_adjoint_comp_thickenedSheafMap {T : RingedSpace.{u, u}}
    (p : Q₁.X' ⟶ T) :
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
        (Q₁.i.hom.base ≫ p.hom.base)).homEquiv _ _).symm (Q₁.comorphismOnOpensSheafMap p) ≫
        Q₁.thickenedSheafMap Q₂ φ hφ =
      eqToHom (by rw [Q₁.base_comp_eq Q₂ φ hφ p]) ≫
        ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
          (Q₂.i.hom.base ≫ (φ ≫ p).hom.base)).homEquiv _ _).symm
          (Q₂.comorphismOnOpensSheafMap (φ ≫ p)) := by
  refine ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    (Q₁.i.hom.base ≫ p.hom.base)).homEquiv_naturality_right_symm _ _).symm.trans ?_
  refine TopCat.Sheaf.pullbackPushforwardAdjunction_homEquiv_symm_eq_eqToHom_comp
    (Q₁.base_comp_eq Q₂ φ hφ p) _ _ fun V => CommRingCat.hom_ext (RingHom.ext fun s => ?_)
  have hW₂ : (Opens.map (φ ≫ p).hom.base).obj V.unop =
      (Opens.map Q₂.baseIso.inv).obj ((Opens.map (Q₁.i.hom.base ≫ p.hom.base)).obj V.unop) := by
    rw [Q₁.base_comp_eq Q₂ φ hφ p]
    exact Q₂.opens_map_comp_eq (φ ≫ p) V.unop
  refine (Q₁.thickenedSheafMap_app_c_app Q₂ φ hφ p V.unop _ (Q₁.opens_map_comp_eq p V.unop)
    hW₂ s).trans ?_
  exact (presheaf_map_map_apply Q₂.X'.presheaf _ _ _ _).symm

/-- Transporting the algebra structure given by a morphism along an equality of morphisms. -/
theorem eqToHom_comp_comorphismOnOpens_adjoint_congr
    {X S S' : RingedSpace.{u, u}} {t : S ⟶ S'} {ht : IsFirstOrderThickening t} {f : X ⟶ S}
    {G : SheafOfModules.{u} (structureSheafRing X)}
    {c : (modulePullback f).obj
      ((modulePullback t).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶ G}
    (Q : DeformationSolution t ht f G c) {T : RingedSpace.{u, u}} {q q' : Q.X' ⟶ T} (hq : q = q')
    {W : TopCat.Sheaf CommRingCat.{u} X.carrier}
    (e : W = (TopCat.Sheaf.pullback CommRingCat.{u} (Q.i.hom.base ≫ q.hom.base)).obj T.sheaf)
    (e' : W = (TopCat.Sheaf.pullback CommRingCat.{u} (Q.i.hom.base ≫ q'.hom.base)).obj T.sheaf) :
    eqToHom e ≫ ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
        (Q.i.hom.base ≫ q.hom.base)).homEquiv _ _).symm (Q.comorphismOnOpensSheafMap q) =
      eqToHom e' ≫ ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
        (Q.i.hom.base ≫ q'.hom.base)).homEquiv _ _).symm (Q.comorphismOnOpensSheafMap q') := by
  subst hq
  rfl

end AlgebraicGeometry.RingedSpaceThickening.DeformationSolution
