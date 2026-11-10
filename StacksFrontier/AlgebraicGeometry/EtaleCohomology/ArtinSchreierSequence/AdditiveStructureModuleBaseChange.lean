module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.QuasiCoherentBaseChange.Main
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.GaCohomologyAddEquiv

/-!
# Base change of the étale cohomology of `𝐆_a`

For a morphism of schemes `g : Y ⟶ X`, pulling back global functions along `T ×_X Y ⟶ T` is a
morphism `𝐆_{a,X} ⟶ g_* 𝐆_{a,Y}` of abelian sheaves on `X_étale`, which is a ring map on every
section and therefore commutes with the Frobenius and with multiplication by global functions.
Its adjoint `g⁻¹ 𝐆_{a,X} ⟶ 𝐆_{a,Y}` composed with restriction is the base change map on the étale
cohomology of `𝐆_a`, and under `𝒪ᵉ ≅ 𝐆_a` (Stacks 03P6) it is the base change map of the
structure module of `AlgebraicGeometry.QcohEtale.restriction`.

## Main definitions

* `Stacks.ArtinSchreier.gaUnit`: pulling back global functions, `𝐆_{a,X} ⟶ g_* 𝐆_{a,Y}`.
* `Stacks.ArtinSchreier.gaComparison`: its adjoint `g⁻¹ 𝐆_{a,X} ⟶ 𝐆_{a,Y}`.
* `Stacks.ArtinSchreier.gaRestriction`: the base change map on the étale cohomology of `𝐆_a`.

## Main results

* `Stacks.ArtinSchreier.gaRestriction_frobenius`: the base change map commutes with the Frobenius.
* `Stacks.ArtinSchreier.gaRestriction_scalar`: the base change map is semilinear.
* `Stacks.ArtinSchreier.gaRestriction_unitEtaleIso`: under `𝒪ᵉ ≅ 𝐆_a` it is the base change map
  of the structure module.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry AlgebraicGeometry.QcohEtale Stacks.EtaleCohomology

universe w u

namespace Stacks.ArtinSchreier

section Unit

variable {X Y : Scheme.{u}} (g : Y ⟶ X)

/-- The pushforward of abelian sheaves along `g`. -/
abbrev etalePush :
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (smallEtaleBaseChange g).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    X.smallEtaleTopology Y.smallEtaleTopology

/-- The adjunction `g⁻¹ ⊣ g_*` on abelian sheaves. -/
abbrev etaleAdj : etaleAbelianInverseImage.{u, u + 1} g ⊣ etalePush g :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (smallEtaleBaseChange g)
    AddCommGrpCat.{u + 1} X.smallEtaleTopology Y.smallEtaleTopology

/-- The projection `T ×_X Y ⟶ T`. -/
abbrev counitLeft (T : X.Etale) : ((baseChangeOver g).obj T).left ⟶ T.left :=
  ((baseChangeCounit g).app T).left

/-- The projections `T ×_X Y ⟶ T` are natural in `T`. -/
theorem counitLeft_naturality {T T' : X.Etale} (m : T' ⟶ T) :
    ((smallEtaleBaseChange g).map m).left ≫ counitLeft g T = counitLeft g T' ≫ m.left :=
  congrArg (fun k => k.left) ((baseChangeCounit g).naturality m)

/-- **Pulling back global functions**, as a morphism `𝐆_{a,X} ⟶ g_* 𝐆_{a,Y}`. -/
def gaUnit : additiveSheaf.{u, u + 1} X ⟶ (etalePush g).obj (additiveSheaf.{u, u + 1} Y) :=
  ⟨{ app := fun T => AddCommGrpCat.ofHom
        (AddEquiv.ulift.symm.toAddMonoidHom.comp
          (((counitLeft g T.unop).appTop).hom.toAddMonoidHom.comp
            AddEquiv.ulift.toAddMonoidHom))
     naturality := fun T T' m => by
        ext x
        change ULift.up ((counitLeft g T'.unop).appTop (m.unop.left.appTop x.down)) =
          ULift.up (((smallEtaleBaseChange g).map m.unop).left.appTop
            ((counitLeft g T.unop).appTop x.down))
        refine congrArg ULift.up ?_
        change (counitLeft g T'.unop ≫ m.unop.left).appTop x.down =
          (((smallEtaleBaseChange g).map m.unop).left ≫ counitLeft g T.unop).appTop x.down
        rw [counitLeft_naturality]
        rfl }⟩

/-- On sections, `gaUnit` is pullback along `T ×_X Y ⟶ T`. -/
theorem gaUnit_app_ofSection (T : X.Etale) (x : Γ(T.left, ⊤)) :
    (gaUnit g).hom.app (op T) (ofSection.{u, u + 1} x) =
      ofSection.{u, u + 1} (X := Y) (U := (smallEtaleBaseChange g).obj T)
        ((counitLeft g T).appTop x) := rfl

/-- **The comparison `g⁻¹ 𝐆_{a,X} ⟶ 𝐆_{a,Y}`.** -/
def gaComparison :
    (etaleAbelianInverseImage.{u, u + 1} g).obj (additiveSheaf.{u, u + 1} X) ⟶
      additiveSheaf.{u, u + 1} Y :=
  ((etaleAdj g).homEquiv _ _).symm (gaUnit g)

/-- Transport of a commuting square along the adjunction. -/
theorem comp_gaComparison {A : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {B : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (a : A ⟶ additiveSheaf.{u, u + 1} X) (b : additiveSheaf.{u, u + 1} Y ⟶ B)
    (c : (etaleAbelianInverseImage.{u, u + 1} g).obj A ⟶ B)
    (h : a ≫ gaUnit g ≫ (etalePush g).map b = (etaleAdj g).homEquiv _ _ c) :
    (etaleAbelianInverseImage.{u, u + 1} g).map a ≫ gaComparison g ≫ b = c := by
  apply ((etaleAdj g).homEquiv _ _).injective
  rw [← h, (etaleAdj g).homEquiv_naturality_left, (etaleAdj g).homEquiv_naturality_right,
    gaComparison, Equiv.apply_symm_apply]

/-- A square through `gaUnit` gives the corresponding square through `gaComparison`. -/
private theorem gaComparison_comm_of_gaUnit
    {a : additiveSheaf.{u, u + 1} X ⟶ additiveSheaf.{u, u + 1} X}
    {b : additiveSheaf.{u, u + 1} Y ⟶ additiveSheaf.{u, u + 1} Y}
    (h : a ≫ gaUnit g = gaUnit g ≫ (etalePush g).map b) :
    (etaleAbelianInverseImage.{u, u + 1} g).map a ≫ gaComparison g = gaComparison g ≫ b := by
  simpa using comp_gaComparison g a (𝟙 _) (gaComparison g ≫ b) (by
    rw [(etaleAdj g).homEquiv_naturality_right, gaComparison, Equiv.apply_symm_apply,
      CategoryTheory.Functor.map_id, Category.comp_id, h])

/-- **Pulling back functions commutes with the Frobenius.** -/
theorem frobeniusMap_comp_gaUnit {p : ℕ} (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0)
    (hY : (p : Γ(Y, ⊤)) = 0) :
    frobeniusMap.{u, u + 1} X hp hX ≫ gaUnit g =
      gaUnit g ≫ (etalePush g).map (frobeniusMap.{u, u + 1} Y hp hY) := by
  ext T x
  obtain ⟨x, rfl⟩ := ofSection_surjective.{u, u + 1} (U := T.unop) x
  change ULift.up ((counitLeft g T.unop).appTop (x ^ p)) =
    ULift.up (((counitLeft g T.unop).appTop x) ^ p)
  exact congrArg ULift.up (map_pow _ _ _)

/-- **The comparison commutes with the Frobenius.** -/
theorem gaComparison_frobenius {p : ℕ} (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0)
    (hY : (p : Γ(Y, ⊤)) = 0) :
    (etaleAbelianInverseImage.{u, u + 1} g).map (frobeniusMap.{u, u + 1} X hp hX) ≫
      gaComparison g = gaComparison g ≫ frobeniusMap.{u, u + 1} Y hp hY :=
  gaComparison_comm_of_gaUnit g (frobeniusMap_comp_gaUnit g hp hX hY)

/-- The pullback of a global function to `T ×_X Y`, through `T` or through `Y`. -/
theorem counitLeft_appTop_etaleRestrict (r : Γ(X, ⊤)) (T : X.Etale) :
    (counitLeft g T).appTop (etaleRestrict T r) =
      etaleRestrict ((smallEtaleBaseChange g).obj T) (g.appTop r) :=
  baseChangeCounit_appTop g r T

/-- **Pulling back functions is semilinear.** -/
theorem gaScalar_comp_gaUnit (r : Γ(X, ⊤)) :
    gaScalar r ≫ gaUnit g = gaUnit g ≫ (etalePush g).map (gaScalar (g.appTop r)) := by
  ext T x
  obtain ⟨x, rfl⟩ := ofSection_surjective.{u, u + 1} (U := T.unop) x
  change (gaUnit g).hom.app T ((gaScalar r).hom.app (op T.unop) (ofSection.{u, u + 1} x)) =
    (gaScalar (g.appTop r)).hom.app (op ((smallEtaleBaseChange g).obj T.unop))
      ((gaUnit g).hom.app (op T.unop) (ofSection.{u, u + 1} x))
  rw [gaScalar_app_ofSection, gaUnit_app_ofSection, gaUnit_app_ofSection, map_mul,
    counitLeft_appTop_etaleRestrict]
  exact (gaScalar_app_ofSection (g.appTop r) ((smallEtaleBaseChange g).obj T.unop)
    ((counitLeft g T.unop).appTop x)).symm

/-- **The comparison is semilinear.** -/
theorem gaComparison_scalar (r : Γ(X, ⊤)) :
    (etaleAbelianInverseImage.{u, u + 1} g).map (gaScalar r) ≫ gaComparison g =
      gaComparison g ≫ gaScalar (g.appTop r) :=
  gaComparison_comm_of_gaUnit g (gaScalar_comp_gaUnit g r)

end Unit

section Identification

attribute [local instance] Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback

/-- `ℱ ↦ ℱᵉ` on isomorphisms. -/
def etaleMapIso {X : Scheme.{u}} {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (e : F ≅ G) : etaleSheaf F ≅ etaleSheaf G where
  hom := etaleMap e.hom
  inv := etaleMap e.inv
  hom_inv_id := by rw [← etaleMap_comp, e.hom_inv_id, etaleMap_id]
  inv_hom_id := by rw [← etaleMap_comp, e.inv_hom_id, etaleMap_id]

/-- **`𝒪_Xᵉ ≅ 𝐆_a`** (Stacks 03P6, coefficients raised). -/
def unitEtaleIso (X : Scheme.{u}) : etaleSheaf (Scheme.unitModule X) ≅ additiveSheaf.{u, u + 1} X :=
  (sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).mapIso
    (additiveSheafBaseIsoSmallEtaleAssociatedSheaf X).symm ≪≫ additiveSheafBaseUliftIso X

/-- On sections, `𝒪_Xᵉ ≅ 𝐆_a` is `Scheme.Modules.pullbackUnitIso`. -/
theorem unitEtaleIso_hom_app {X : Scheme.{u}} (T : X.Etale)
    (s : Γ((Scheme.Modules.pullback T.hom).obj (Scheme.unitModule X), ⊤)) :
    (unitEtaleIso X).hom.hom.app (op T) (ULift.up s) =
      ofSection.{u, u + 1} ((Scheme.Modules.pullbackUnitIso T.hom).hom.app ⊤ s) := rfl

variable {X Y : Scheme.{u}} (g : Y ⟶ X)

/-- **`(g^* 𝒪_X)ᵉ ≅ 𝐆_{a,Y}`.** -/
def pullbackUnitEtaleIso :
    etaleSheaf ((Scheme.Modules.pullback g).obj (Scheme.unitModule X)) ≅
      additiveSheaf.{u, u + 1} Y :=
  etaleMapIso (Scheme.Modules.pullbackUnitIso g) ≪≫ unitEtaleIso Y

/-- On sections, `(g^* 𝒪_X)ᵉ ≅ 𝐆_{a,Y}` is the composite of the two `pullbackUnitIso`s. -/
theorem pullbackUnitEtaleIso_hom_app (T : Y.Etale)
    (m : Γ((Scheme.Modules.pullback T.hom).obj
      ((Scheme.Modules.pullback g).obj (Scheme.unitModule X)), ⊤)) :
    (pullbackUnitEtaleIso g).hom.hom.app (op T) (ULift.up m) =
      ofSection.{u, u + 1} ((Scheme.Modules.pullbackUnitIso T.hom).hom.app ⊤
        (((Scheme.Modules.pullback T.hom).map (Scheme.Modules.pullbackUnitIso g).hom).app ⊤ m)) :=
  rfl

/-- **The two units agree under `𝒪ᵉ ≅ 𝐆_a`.** -/
theorem unitEtaleIso_comp_gaUnit :
    (unitEtaleIso X).hom ≫ gaUnit g =
      unit g (Scheme.unitModule X) ≫ (etalePush g).map (pullbackUnitEtaleIso g).hom := by
  ext T s
  obtain ⟨s⟩ := s
  let A := (baseChangeOver g).obj T.unop
  let c := (baseChangeCounit g).app T.unop
  change ofSection.{u, u + 1} ((counitLeft g T.unop).appTop
      ((Scheme.Modules.pullbackUnitIso T.unop.hom).hom.app ⊤ s)) =
    ofSection.{u, u + 1} ((Scheme.Modules.pullbackUnitIso A.hom).hom.app ⊤
      (((Scheme.Modules.pullback A.hom).map (Scheme.Modules.pullbackUnitIso g).hom).app ⊤
        (((Scheme.Modules.pullbackComp A.hom g).inv.app (Scheme.unitModule X)).app ⊤
          (pullbackSectionsMap (Scheme.unitModule X) c s))))
  refine congrArg ofSection.{u, u + 1} ?_
  have h2 := ConcreteCategory.congr_hom (congrArg (fun φ => Scheme.Modules.Hom.app φ ⊤)
    (Scheme.Modules.pullbackUnitIso_comp A.hom g)) (pullbackSectionsMap (Scheme.unitModule X) c s)
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at h2
  exact (pullbackUnitIso_hom_app_top_pullbackSectionsMap c s).symm.trans h2.symm

/-- `𝒪ᵉ ≅ 𝐆_a` intertwines multiplication by global functions. -/
theorem etaleScalar_comp_unitEtaleIso (r : Γ(Y, ⊤)) :
    etaleScalar (Scheme.unitModule Y) r ≫ (unitEtaleIso Y).hom =
      (unitEtaleIso Y).hom ≫ gaScalar r := by
  ext T x
  obtain ⟨x⟩ := x
  exact congrArg ULift.up (Scheme.Modules.Hom.app_smul
    (Scheme.Modules.pullbackUnitIso T.unop.hom).hom (T.unop.hom.appTop r) x)

/-- `(g^* 𝒪_X)ᵉ ≅ 𝐆_{a,Y}` intertwines multiplication by global functions. -/
theorem etaleScalar_comp_pullbackUnitEtaleIso (r : Γ(Y, ⊤)) :
    etaleScalar ((Scheme.Modules.pullback g).obj (Scheme.unitModule X)) r ≫
        (pullbackUnitEtaleIso g).hom =
      (pullbackUnitEtaleIso g).hom ≫ gaScalar r := by
  change _ ≫ etaleMap (Scheme.Modules.pullbackUnitIso g).hom ≫ (unitEtaleIso Y).hom =
    (etaleMap (Scheme.Modules.pullbackUnitIso g).hom ≫ (unitEtaleIso Y).hom) ≫ gaScalar r
  rw [← Category.assoc, etaleScalar_comp_etaleMap, Category.assoc,
    etaleScalar_comp_unitEtaleIso, Category.assoc]

/-- **The two comparisons agree under `𝒪ᵉ ≅ 𝐆_a`.** -/
theorem gaComparison_unitEtaleIso :
    (etaleAbelianInverseImage.{u, u + 1} g).map (unitEtaleIso X).hom ≫ gaComparison g =
      comparison g (Scheme.unitModule X) ≫ (pullbackUnitEtaleIso g).hom := by
  apply ((etaleAdj g).homEquiv _ _).injective
  rw [(etaleAdj g).homEquiv_naturality_left, (etaleAdj g).homEquiv_naturality_right,
    gaComparison, Equiv.apply_symm_apply]
  change _ = (etaleAdj g).homEquiv _ _ (((etaleAdj g).homEquiv _ _).symm
      (unit g (Scheme.unitModule X))) ≫ _
  rw [Equiv.apply_symm_apply, unitEtaleIso_comp_gaUnit]

end Identification

section Restriction

variable {X Y : Scheme.{u}} (g : Y ⟶ X)
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **The base change map on the étale cohomology of `𝐆_a`.** -/
def gaRestriction (q : ℕ) :
    Sheaf.H.{w} (additiveSheaf.{u, u + 1} X) q →+ Sheaf.H.{w} (additiveSheaf.{u, u + 1} Y) q :=
  ((Ext.mk₀ (gaComparison g)).postcomp _ (add_zero q)).comp
    (etaleCohomologyRestrictionMap.{u, u + 1, w} g (additiveSheaf.{u, u + 1} X) q)

/-- The base change map is restriction followed by composition with `gaComparison`. -/
theorem gaRestriction_apply (q : ℕ) (x : Sheaf.H.{w} (additiveSheaf.{u, u + 1} X) q) :
    gaRestriction g q x =
      (etaleCohomologyRestrictionMap.{u, u + 1, w} g (additiveSheaf.{u, u + 1} X) q x).comp
        (Ext.mk₀ (gaComparison g)) (add_zero q) := rfl

/-- A square `g⁻¹ a ≫ gaComparison = c ≫ b` gives a square on cohomology. -/
private theorem gaRestriction_map_comp_eq
    {A : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {B : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (a : A ⟶ additiveSheaf.{u, u + 1} X) (c : (etaleAbelianInverseImage.{u, u + 1} g).obj A ⟶ B)
    (b : B ⟶ additiveSheaf.{u, u + 1} Y)
    (h : (etaleAbelianInverseImage.{u, u + 1} g).map a ≫ gaComparison g = c ≫ b)
    (q : ℕ) (x : Sheaf.H.{w} A q) :
    gaRestriction g q (Sheaf.H.map a q x) =
      Sheaf.H.map b q
        ((etaleCohomologyRestrictionMap.{u, u + 1, w} g A q x).comp (Ext.mk₀ c) (add_zero q)) := by
  change (etaleCohomologyRestrictionMap.{u, u + 1, w} g _ q (x.comp (Ext.mk₀ a) (add_zero q))).comp
      (Ext.mk₀ (gaComparison g)) (add_zero q) =
    ((etaleCohomologyRestrictionMap.{u, u + 1, w} g _ q x).comp (Ext.mk₀ c)
      (add_zero q)).comp (Ext.mk₀ b) (add_zero q)
  rw [etaleCohomologyRestrictionMap_comp_mk₀, Ext.comp_assoc_of_third_deg_zero,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀, h]

/-- A square of sheaf maps through the comparison gives a square on cohomology. -/
theorem gaRestriction_map {a : additiveSheaf.{u, u + 1} X ⟶ additiveSheaf.{u, u + 1} X}
    {b : additiveSheaf.{u, u + 1} Y ⟶ additiveSheaf.{u, u + 1} Y}
    (h : (etaleAbelianInverseImage.{u, u + 1} g).map a ≫ gaComparison g = gaComparison g ≫ b)
    (q : ℕ) (x : Sheaf.H.{w} (additiveSheaf.{u, u + 1} X) q) :
    gaRestriction g q (Sheaf.H.map a q x) = Sheaf.H.map b q (gaRestriction g q x) :=
  gaRestriction_map_comp_eq g a _ b h q x

/-- **The base change map commutes with the Frobenius.** -/
theorem gaRestriction_frobenius {p : ℕ} (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0)
    (hY : (p : Γ(Y, ⊤)) = 0) (q : ℕ) (x : Sheaf.H.{w} (additiveSheaf.{u, u + 1} X) q) :
    gaRestriction g q (Sheaf.H.map (frobeniusMap.{u, u + 1} X hp hX) q x) =
      Sheaf.H.map (frobeniusMap.{u, u + 1} Y hp hY) q (gaRestriction g q x) :=
  gaRestriction_map g (gaComparison_frobenius g hp hX hY) q x

/-- **The base change map is semilinear.** -/
theorem gaRestriction_scalar (r : Γ(X, ⊤)) (q : ℕ)
    (x : Sheaf.H.{w} (additiveSheaf.{u, u + 1} X) q) :
    gaRestriction g q (Sheaf.H.map (gaScalar r) q x) =
      Sheaf.H.map (gaScalar (g.appTop r)) q (gaRestriction g q x) :=
  gaRestriction_map g (gaComparison_scalar g r) q x

attribute [local instance] Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback in
/-- **The base change map of `𝐆_a` is the base change map of the structure module.** -/
theorem gaRestriction_unitEtaleIso (q : ℕ)
    (x : Sheaf.H.{w} (etaleSheaf (Scheme.unitModule X)) q) :
    gaRestriction g q (Sheaf.H.map (unitEtaleIso X).hom q x) =
      Sheaf.H.map (pullbackUnitEtaleIso g).hom q (restriction g (Scheme.unitModule X) q x) := by
  exact gaRestriction_map_comp_eq g _ _ _ (gaComparison_unitEtaleIso g) q x

end Restriction

end Stacks.ArtinSchreier

end
