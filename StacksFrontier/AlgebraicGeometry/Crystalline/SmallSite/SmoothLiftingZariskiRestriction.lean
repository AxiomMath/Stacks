module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SelfProductConormal
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AmbientRestrictionDerived
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisZariskiSquareEval07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.GlobalSectionsIsoRestriction
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusNatIsoGlue
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianBaseChangeMapFunctoriality

/-!
# Restricting `u_{X/S, *}` to the ambient scheme of an object of `Cris(X/S)`

Fix a global crystalline situation `(p, (S, I, γ), X)` and an object `A = (U, T, δ)` of the small
crystalline site `Cris(X/S)`.  The immersion `U ⟶ T` is a homeomorphism
(`Crystalline.GlobalCrystallineSituation.isHomeomorph_thickeningImmersion`), so composing its
inverse with the open immersion `U ⟶ X` gives a continuous map `h : T ⟶ X`, under which the
open `h⁻¹(W)` of `T` corresponding to an open `W` of `X` is the open with `h⁻¹(W) ∩ U = W ∩ U`.
Write `h_*` for the pushforward of abelian sheaves on `T_Zar` along `h`.

For an abelian sheaf `G` on `Cris(X/S)` a section of `u_{X/S, *}G` over `W` is a compatible family
of sections of `G` over the objects of `Cris(X/S)` lying over `W`; the restriction `A|_{h⁻¹(W)}`
lies over `W`, so the family has a value there, which is a section of `G_T` over `h⁻¹(W)`, that
is, of `h_*(G_T)` over `W`.  This gives a natural transformation

`u_{X/S, *}G ⟶ h_*(G_T)`

of abelian sheaves on `X_Zar`, natural in `G`.  On global sections it is the restriction
`Γ(Cris(X/S), G) ⟶ Γ(T, G_T)` of `CrystallineThickening.globalSectionsToAmbient`.

Deriving it gives, for a bounded below complex `K` of abelian sheaves on `Cris(X/S)`, a natural
map `Ru_{X/S, *}K ⟶ Rh_*(K_T)` in `D⁺(Ab(X_Zar))`, where `Rh_*` is the right derived functor of
`h_*` (which preserves injectives); on derived global sections, through
`RΓ(Cris(X/S), K) ≅ RΓ(X_Zar, Ru_{X/S, *}K)` and `RΓ(X_Zar, Rh_*(K_T)) ≅ RΓ(T, K_T)`, it is the
derived restriction `CrystallineThickening.derivedGlobalSectionsToAmbient` of [Stacks, Equation
07LP].

When `U = X` (as for the object attached to a smooth lifting of `X`), `h` is a homeomorphism
`T ≅ X` and `h_*` identifies abelian sheaves on `T_Zar` with abelian sheaves on `X_Zar`.  Nothing
in this file needs that hypothesis, and nothing here identifies `Rh_*` with `h_*` (that `h_*` is
exact when `h` is a homeomorphism is not proved here).

## Main definitions

Everything lives in the namespace
`Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening`.

* `ambientToX` — the continuous map `h : T ⟶ X`, the inverse of `U ≅ T` followed by `U ⟶ X`.
* `ambientToXPreimage` — the open `h⁻¹(W)` of `T` attached to an open `W` of `X`.
* `ambientPushforward` — `h_* : Ab(T_Zar) ⥤ Ab(X_Zar)`.
* `zariskiDirectImageToAmbient` — **the natural transformation `u_{X/S, *}G ⟶ h_*(G_T)`**.
* `ambientPushforwardGlobalSectionsIso` — `Γ(X_Zar, h_* -) ≅ Γ(T, -)`.
* `derivedAmbientPushforwardFunctor` — `Rh_* : D⁺(Ab(T_Zar)) ⥤ D⁺(Ab(X_Zar))`.
* `zariskiDirectImageToAmbientComparison` and `derivedZariskiDirectImageToAmbient` — **the derived
  transformation `Ru_{X/S, *}K ⟶ Rh_*(K_T)`**, characterised on complexes by
  `derivedZariskiDirectImageToAmbient_fac_app`.
* `derivedAmbientPushforwardGlobalSectionsIso` — `RΓ(X_Zar, Rh_* -) ≅ RΓ(T, -)`.

## Main results

* `immersion_preimage_ambientToXPreimage` and `ambientToXPreimage_eq_of_preimage_eq` — `h⁻¹(W)` is
  the unique open `V` of `T` whose preimage in `U` is the preimage of `W`.
* `zariskiDirectImageToAmbient_app_hom_app` — over `W` the transformation is the value of a
  family at `A|_{h⁻¹(W)}`, `zariskiDirectImageEval`.
* `zariskiDirectImageToAmbient_app_hom_app_comp` and
  `zariskiDirectImageEval_eq_zariskiDirectImageToAmbient` — the value of a family at an object
  over `W` mapping to `A|_{h⁻¹(W)}`, or at the restriction of `A` to any open `V` of `T` with
  `V ∩ U = W ∩ U`, is read off the transformation.
* `zariskiDirectImageToAmbient_globalSections` — **on global sections the transformation is
  `globalSectionsToAmbient`**, through `zariskiGlobalSectionsDirectImageIso` and
  `ambientPushforwardGlobalSectionsIso`; `zariskiDirectImageToAmbient_globalSections_natTrans` is
  the same as an equation of natural transformations.
* `preservesInjectiveObjects_ambientPushforward` — `h_*` preserves injective abelian sheaves.
* `derivedZariskiDirectImageToAmbient_fac_app` — on a bounded below complex, the derived
  transformation precomposed with `u_{X/S, *}K ⟶ Ru_{X/S, *}K` is the termwise transformation
  followed by `h_*(K_T) ⟶ Rh_*(K_T)` (`zariskiDirectImageToAmbientComparison_app`).
* `derivedZariskiDirectImageToAmbient_globalSections` — **on derived global sections the derived
  transformation is `derivedGlobalSectionsToAmbient`**.

## References

* [Stacks Project, Tag 07LP](https://stacks.math.columbia.edu/tag/07LP)
* [Stacks Project, Tag 07MW](https://stacks.math.columbia.edu/tag/07MW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe w w' w'' w''' u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

namespace CrystallineThickening

variable {S : GlobalCrystallineSituation.{u}} (A : CrystallineThickening S)

/-! ### The map `h : T ⟶ X` -/

/-- **The homeomorphism `U ≃ₜ T`** given by the immersion of the thickening of `A`. -/
def thickeningHomeomorph : A.obj.thickening.source ≃ₜ A.obj.thickening.target.scheme :=
  IsHomeomorph.homeomorph _ (isHomeomorph_thickeningImmersion A.obj.thickening)

/-- The homeomorphism `U ≃ₜ T` is the immersion of the thickening. -/
@[simp]
theorem thickeningHomeomorph_apply (x : A.obj.thickening.source) :
    thickeningHomeomorph A x = A.obj.thickening.immersion x :=
  rfl

/-- **The continuous map `h : T ⟶ X`**: the inverse of the homeomorphism `U ≃ₜ T` followed by the
structure map `U ⟶ X`. -/
def ambientToX : A.obj.thickening.target.scheme.carrier ⟶ S.X.carrier :=
  TopCat.ofHom ⟨(thickeningHomeomorph A).symm, (thickeningHomeomorph A).symm.continuous⟩ ≫
    A.obj.toX.base

/-- `h` composed with the immersion `U ⟶ T` is the structure map `U ⟶ X`. -/
@[simp]
theorem ambientToX_immersion (x : A.obj.thickening.source) :
    ambientToX A (A.obj.thickening.immersion x) = A.obj.toX x := by
  simp only [ambientToX, TopCat.hom_comp, ContinuousMap.comp_apply, TopCat.hom_ofHom,
    ContinuousMap.coe_mk]
  rw [← thickeningHomeomorph_apply, Homeomorph.symm_apply_apply]

/-- **The open `h⁻¹(W)` of `T` attached to an open `W` of `X`.** -/
abbrev ambientToXPreimage (W : S.X.Opens) : A.obj.thickening.target.scheme.Opens :=
  (Opens.map (ambientToX A)).obj W

/-- **The preimage of `h⁻¹(W)` in `U` is the preimage of `W`.** -/
theorem immersion_preimage_ambientToXPreimage (W : S.X.Opens) :
    A.obj.thickening.immersion ⁻¹ᵁ ambientToXPreimage A W = A.obj.toX ⁻¹ᵁ W := by
  ext x
  change ambientToX A (A.obj.thickening.immersion x) ∈ W ↔ A.obj.toX x ∈ W
  rw [ambientToX_immersion]

/-- **`h⁻¹(W)` is the only open of `T` whose preimage in `U` is the preimage of `W`**: an open `V`
of `T` with `V ∩ U = W ∩ U` is `h⁻¹(W)`, the immersion `U ⟶ T` being surjective. -/
theorem ambientToXPreimage_eq_of_preimage_eq {W : S.X.Opens}
    {V : A.obj.thickening.target.scheme.Opens}
    (hV : A.obj.thickening.immersion ⁻¹ᵁ V = A.obj.toX ⁻¹ᵁ W) : ambientToXPreimage A W = V := by
  ext t
  obtain ⟨x, rfl⟩ := (thickeningHomeomorph A).surjective t
  rw [thickeningHomeomorph_apply]
  change A.obj.thickening.immersion x ∈ ambientToXPreimage A W ↔ A.obj.thickening.immersion x ∈ V
  change x ∈ A.obj.thickening.immersion ⁻¹ᵁ ambientToXPreimage A W ↔
    x ∈ A.obj.thickening.immersion ⁻¹ᵁ V
  rw [immersion_preimage_ambientToXPreimage, hV]

/-- **The restriction of `A` to an open `V` of `T` lies over every open `W` of `X` with
`V ∩ U ⊆ W`.** -/
theorem forgetToOpens_restrictOpen_le {W : S.X.Opens} {V : A.obj.thickening.target.scheme.Opens}
    (hV : A.obj.thickening.immersion ⁻¹ᵁ V ≤ A.obj.toX ⁻¹ᵁ W) :
    (forgetToOpens S).obj (A.restrictOpen V) ≤ W := by
  change Set.range ((A.obj.thickening.immersion ⁻¹ᵁ V).ι ≫ A.obj.toX) ⊆ W
  rintro _ ⟨x, rfl⟩
  exact hV x.2

/-- **The restriction `A|_{h⁻¹(W)}` lies over `W`.** -/
theorem forgetToOpens_restrictOpen_ambientToXPreimage_le (W : S.X.Opens) :
    (forgetToOpens S).obj (A.restrictOpen (ambientToXPreimage A W)) ≤ W :=
  forgetToOpens_restrictOpen_le A (immersion_preimage_ambientToXPreimage A W).le

/-! ### The pushforward `h_*` -/

/-- **The pushforward `h_* : Ab(T_Zar) ⥤ Ab(X_Zar)`** along `h : T ⟶ X`; on sections it is
`(h_* F)(W) = F(h⁻¹(W))`. -/
def ambientPushforward :
    Sheaf (Opens.grothendieckTopology A.obj.thickening.target.scheme) AddCommGrpCat.{u + 1} ⥤
      Sheaf (opensTopology S) AddCommGrpCat.{u + 1} :=
  (Opens.map (ambientToX A)).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (opensTopology S) (Opens.grothendieckTopology A.obj.thickening.target.scheme)

/-- The sections of `h_* F` over an open `W` of `X` are the sections of `F` over `h⁻¹(W)`. -/
theorem ambientPushforward_obj_obj_obj
    (F : Sheaf (Opens.grothendieckTopology A.obj.thickening.target.scheme) AddCommGrpCat.{u + 1})
    (W : S.X.Opens) :
    ((ambientPushforward A).obj F).obj.obj (op W) = F.obj.obj (op (ambientToXPreimage A W)) :=
  rfl

/-- `h_*` is additive. -/
instance additive_ambientPushforward : (ambientPushforward A).Additive where
  map_add := by intros; rfl

/-! ### The transformation `u_{X/S, *}G ⟶ h_*(G_T)` -/

/-- The component at an abelian sheaf `G` of `zariskiDirectImageToAmbient`: over an open `W` of
`X`, the value of a section of `u_{X/S, *}G` at the restriction `A|_{h⁻¹(W)}`. -/
def zariskiDirectImageToAmbientApp (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :
    (zariskiDirectImage S).obj G ⟶
      (ambientPushforward A).obj ((abelianAmbientRestriction A).obj G) :=
  ObjectProperty.homMk
    { app W :=
        zariskiDirectImageEval S (forgetToOpens_restrictOpen_ambientToXPreimage_le A W.unop) G
      naturality {W W'} i :=
        (zariskiDirectImageEval_restrict S (leOfHom i.unop)
          (forgetToOpens_restrictOpen_ambientToXPreimage_le A W'.unop) G).trans
          (zariskiDirectImageEval_comp S
            (restrictOpenLE A ((Opens.map (ambientToX A)).monotone (leOfHom i.unop)))
            ((forgetToOpens_restrictOpen_ambientToXPreimage_le A W'.unop).trans (leOfHom i.unop))
            (forgetToOpens_restrictOpen_ambientToXPreimage_le A W.unop) G).symm }

/-- **The natural transformation `u_{X/S, *}G ⟶ h_*(G_T)`**, natural in the abelian sheaf `G` on
`Cris(X/S)`.  Over an open `W` of `X` it sends a section of `u_{X/S, *}G`, a compatible family of
sections of `G` over the objects of `Cris(X/S)` lying over `W`, to its value at the restriction
`A|_{h⁻¹(W)}` of `A` to the open `h⁻¹(W)` of `T` (`zariskiDirectImageToAmbient_app_hom_app`). -/
def zariskiDirectImageToAmbient :
    zariskiDirectImage S ⟶ abelianAmbientRestriction A ⋙ ambientPushforward A where
  app G := zariskiDirectImageToAmbientApp A G
  naturality G H φ := by
    exact Sheaf.hom_ext (NatTrans.ext (funext fun W =>
      zariskiDirectImageEval_naturality S
        (forgetToOpens_restrictOpen_ambientToXPreimage_le A W.unop) φ))

/-- **The transformation `u_{X/S, *}G ⟶ h_*(G_T)` on sections over `W`** is the value at
`A|_{h⁻¹(W)}`, `zariskiDirectImageEval`. -/
theorem zariskiDirectImageToAmbient_app_hom_app
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (W : S.X.Opens) :
    ((zariskiDirectImageToAmbient A).app G).hom.app (op W) =
      zariskiDirectImageEval S (forgetToOpens_restrictOpen_ambientToXPreimage_le A W) G :=
  rfl

/-- **The value of a section of `u_{X/S, *}G` at an object over `W` mapping to `A|_{h⁻¹(W)}`** is
the transformation followed by the restriction along that map. -/
@[reassoc]
theorem zariskiDirectImageToAmbient_app_hom_app_comp
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (W : S.X.Opens)
    {B : CrystallineThickening S} (g : B ⟶ A.restrictOpen (ambientToXPreimage A W))
    (hB : (forgetToOpens S).obj B ≤ W) :
    ((zariskiDirectImageToAmbient A).app G).hom.app (op W) ≫ G.obj.map g.op =
      zariskiDirectImageEval S hB G :=
  zariskiDirectImageEval_comp S g hB _ G

/-- **The value of a section of `u_{X/S, *}G` at the restriction of `A` to an open `V` of `T` with
`V ∩ U = W ∩ U`** is the transformation over `W`, followed by the identification
`A|_V = A|_{h⁻¹(W)}` of `ambientToXPreimage_eq_of_preimage_eq`. -/
theorem zariskiDirectImageEval_eq_zariskiDirectImageToAmbient
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) {W : S.X.Opens}
    {V : A.obj.thickening.target.scheme.Opens}
    (hV : A.obj.thickening.immersion ⁻¹ᵁ V = A.obj.toX ⁻¹ᵁ W) :
    zariskiDirectImageEval S (forgetToOpens_restrictOpen_le A hV.le) G =
      ((zariskiDirectImageToAmbient A).app G).hom.app (op W) ≫
        G.obj.map (restrictOpenLE A (ambientToXPreimage_eq_of_preimage_eq A hV).ge).op :=
  (zariskiDirectImageToAmbient_app_hom_app_comp A G W _ _).symm

/-! ### Global sections -/

/-- **`Γ(X_Zar, h_* F) ≅ Γ(T, F)`**, naturally in the abelian sheaf `F` on `T_Zar`: both are the
sections over the top open, and `h⁻¹(⊤) = ⊤` definitionally. -/
def ambientPushforwardGlobalSectionsIso :
    ambientPushforward A ⋙ zariskiGlobalSections S ≅ ambientGlobalSections A :=
  Functor.isoWhiskerLeft (ambientPushforward A)
      (Sheaf.ΓNatIsoSheafSections (opensTopology S) AddCommGrpCat.{u + 1}
        (isTerminalTop (α := S.X.Opens))) ≪≫
    (Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      AddCommGrpCat.{u + 1} (isTerminalTop (α := A.obj.thickening.target.scheme.Opens))).symm

/-- `Γ(X_Zar, h_* F) ≅ Γ(T, F)` read against the restriction maps to the top opens. -/
@[reassoc (attr := simp)]
theorem ambientPushforwardGlobalSectionsIso_hom_app_comp_ΓRes
    (F : Sheaf (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      AddCommGrpCat.{u + 1}) :
    (ambientPushforwardGlobalSectionsIso A).hom.app F ≫ Sheaf.ΓRes F (op ⊤) =
      Sheaf.ΓRes ((ambientPushforward A).obj F) (op ⊤) := by
  have h₁ := Sheaf.ΓNatIsoSheafSections_hom_app_general
    (isTerminalTop (α := A.obj.thickening.target.scheme.Opens)) F
  have h₂ := Sheaf.ΓNatIsoSheafSections_hom_app_general
    (isTerminalTop (α := S.X.Opens)) ((ambientPushforward A).obj F)
  rw [← h₁, ← h₂]
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Iso.inv_hom_id_app _ F)).trans
    (Category.comp_id _))

/-- **On global sections, `u_{X/S, *}G ⟶ h_*(G_T)` is the restriction
`Γ(Cris(X/S), G) ⟶ Γ(T, G_T)`**: through `Γ(X_Zar, u_{X/S, *}G) ≅ Γ(Cris(X/S), G)` and
`Γ(X_Zar, h_*(G_T)) ≅ Γ(T, G_T)`, it is `globalSectionsToAmbient`. -/
theorem zariskiDirectImageToAmbient_globalSections
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :
    (zariskiGlobalSectionsDirectImageIso S).inv.app G ≫
        (zariskiGlobalSections S).map ((zariskiDirectImageToAmbient A).app G) ≫
          (ambientPushforwardGlobalSectionsIso A).hom.app
            ((abelianAmbientRestriction A).obj G) =
      (globalSectionsToAmbient A).app G := by
  have hR : (globalSectionsToAmbient A).app G ≫
      Sheaf.ΓRes ((abelianAmbientRestriction A).obj G) (op ⊤) =
      Sheaf.ΓRes G (op (A.restrictOpen (ambientToXPreimage A ⊤))) := by
    rw [← Sheaf.ΓNatIsoLim_hom_app_comp_π, ← Sheaf.ΓNatIsoLim_hom_app_comp_π]
    exact globalSectionsToAmbient_app_comp A G ⊤
  have hL := zariskiGlobalSectionsDirectImageIso_hom_app_comp_ΓRes S G
    (A.restrictOpen (ambientToXPreimage A ⊤))
  have hM : Sheaf.ΓRes ((zariskiDirectImage S).obj G) (op ⊤) ≫
      ((zariskiDirectImageToAmbient A).app G).hom.app (op ⊤) =
      Sheaf.ΓRes ((zariskiDirectImage S).obj G)
          (op ((forgetToOpens S).obj (A.restrictOpen (ambientToXPreimage A ⊤)))) ≫
        ((forgetToOpens S).op.ranCounit.app G.obj).app
          (op (A.restrictOpen (ambientToXPreimage A ⊤))) := by
    rw [zariskiDirectImageToAmbient_app_hom_app, zariskiDirectImageEval]
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (Sheaf.ΓRes_map _ _))
  rw [← Iso.cancel_iso_hom_right _ _ ((Sheaf.ΓNatIsoSheafSections
      (Opens.grothendieckTopology A.obj.thickening.target.scheme) AddCommGrpCat.{u + 1}
      (isTerminalTop (α := A.obj.thickening.target.scheme.Opens))).app
        ((abelianAmbientRestriction A).obj G)), Iso.app_hom,
    Sheaf.ΓNatIsoSheafSections_hom_app_general, hR]
  simp only [Category.assoc]
  rw [ambientPushforwardGlobalSectionsIso_hom_app_comp_ΓRes]
  exact (congrArg (_ ≫ ·) (Sheaf.ΓRes_naturality ((zariskiDirectImageToAmbient A).app G)
    (op ⊤))).trans (by rw [hM, ← hL]; exact Iso.inv_hom_id_app_assoc _ _ _)

/-- `zariskiDirectImageToAmbient_globalSections` as an equation of natural transformations. -/
theorem zariskiDirectImageToAmbient_globalSections_natTrans :
    (zariskiGlobalSectionsDirectImageIso S).inv ≫
        Functor.whiskerRight (zariskiDirectImageToAmbient A) (zariskiGlobalSections S) ≫
          (Functor.associator _ _ _).hom ≫
            Functor.whiskerLeft (abelianAmbientRestriction A)
              (ambientPushforwardGlobalSectionsIso A).hom =
      globalSectionsToAmbient A := by
  ext G : 2
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp]
  exact zariskiDirectImageToAmbient_globalSections A G

/-! ### The derived transformation `Ru_{X/S, *}K ⟶ Rh_*(K_T)` -/

section Derived

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **`h_*` carries injective abelian sheaves to injective abelian sheaves**, its left adjoint
being exact. -/
instance preservesInjectiveObjects_ambientPushforward :
    (ambientPushforward A).PreservesInjectiveObjects :=
  haveI : HasSheafify (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      AddCommGrpCat.{u + 1} := GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u} _
  haveI : HasSheafify (Opens.grothendieckTopology S.X.carrier) AddCommGrpCat.{u + 1} :=
    instHasSheafifyOpensAddCommGrpCat S
  Stacks.Topology.preservesInjectiveObjects_sheafPushforwardOpensMap.{u + 1} (ambientToX A)

/-- The termwise form of the derived comparison: on bounded below homotopy categories, the
isomorphism `Γ(X_Zar, u_{X/S, *} -) ≅ Γ(Cris(X/S), -)`, then `Γ(X_Zar, -)` of the termwise
transformation, then `Γ(X_Zar, h_* -) ≅ Γ(T, -)`, is the termwise restriction to `T`.  The
statement typechecks because the functors induced by a composite and the composite of the
induced functors agree on objects. -/
theorem mapHomotopyCategoryPlus_zariskiDirectImageToAmbient_globalSections
    (K : HomotopyCategory.Plus (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})) :
    (Functor.mapHomotopyCategoryPlusNatIso (zariskiGlobalSectionsDirectImageIso S)).inv.app K ≫
        (zariskiGlobalSections S).mapHomotopyCategoryPlus.map
          ((Functor.mapHomotopyCategoryPlusNatTrans (zariskiDirectImageToAmbient A)).app K) ≫
        (Functor.mapHomotopyCategoryPlusNatIso (ambientPushforwardGlobalSectionsIso A)).hom.app
          ((abelianAmbientRestriction A).mapHomotopyCategoryPlus.obj K) =
      (Functor.mapHomotopyCategoryPlusNatTrans (globalSectionsToAmbient A)).app K := by
  have hz : (Functor.mapHomotopyCategoryPlusNatIso
      (zariskiGlobalSectionsDirectImageIso S)).inv.app K =
      (Stacks.Cohomology.BaseChange.mapPlus (zariskiGlobalSectionsDirectImageIso S).inv).app K :=
    rfl
  have hη : (zariskiGlobalSections S).mapHomotopyCategoryPlus.map
      ((Functor.mapHomotopyCategoryPlusNatTrans (zariskiDirectImageToAmbient A)).app K) =
      (Stacks.Cohomology.BaseChange.mapPlus (Functor.whiskerRight (zariskiDirectImageToAmbient A)
        (zariskiGlobalSections S))).app K :=
    (Stacks.Cohomology.BaseChange.mapPlus_whiskerRight_app _ _ K).symm
  have hw : (Functor.mapHomotopyCategoryPlusNatIso (ambientPushforwardGlobalSectionsIso A)).hom.app
      ((abelianAmbientRestriction A).mapHomotopyCategoryPlus.obj K) =
      (Stacks.Cohomology.BaseChange.mapPlus (Functor.whiskerLeft (abelianAmbientRestriction A)
        (ambientPushforwardGlobalSectionsIso A).hom)).app K :=
    (Stacks.Cohomology.BaseChange.mapPlus_whiskerLeft_app _ _ K).symm
  have ha : (Stacks.Cohomology.BaseChange.mapPlus (Functor.associator
      (abelianAmbientRestriction A) (ambientPushforward A) (zariskiGlobalSections S)).hom).app K =
      𝟙 _ := by
    rw [show (Functor.associator (abelianAmbientRestriction A) (ambientPushforward A)
      (zariskiGlobalSections S)).hom = 𝟙 _ from rfl, Stacks.Cohomology.BaseChange.mapPlus_id]
    rfl
  have hγ : (Functor.mapHomotopyCategoryPlusNatTrans (globalSectionsToAmbient A)).app K =
      (Stacks.Cohomology.BaseChange.mapPlus (globalSectionsToAmbient A)).app K := rfl
  rw [hz, hη, hw, hγ, ← zariskiDirectImageToAmbient_globalSections_natTrans,
    Stacks.Cohomology.BaseChange.mapPlus_comp, Stacks.Cohomology.BaseChange.mapPlus_comp,
    Stacks.Cohomology.BaseChange.mapPlus_comp, NatTrans.comp_app, NatTrans.comp_app,
    NatTrans.comp_app, ha, Category.id_comp]

variable [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'}
    (Sheaf (Opens.grothendieckTopology A.obj.thickening.target.scheme) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'''} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]

/-- **The derived pushforward `Rh_* : D⁺(Ab(T_Zar)) ⥤ D⁺(Ab(X_Zar))`**, the right derived functor
of `h_*`. -/
abbrev derivedAmbientPushforwardFunctor :
    DerivedCategory.Plus
        (Sheaf (Opens.grothendieckTopology A.obj.thickening.target.scheme)
          AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (opensTopology S) AddCommGrpCat.{u + 1}) :=
  (ambientPushforward A).rightDerivedFunctorPlus

/-- The termwise comparison out of which `derivedZariskiDirectImageToAmbient` is derived: on the
image of a bounded below complex `K`, the termwise transformation `u_{X/S, *}K ⟶ h_*(K_T)`, then
the canonical map `h_*(K_T) ⟶ Rh_*(K_T)`, then the identification of `K_T` with the restriction of
`K` in the derived category. -/
def zariskiDirectImageToAmbientComparison :
    (zariskiDirectImage S).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ derivedAmbientRestriction A ⋙
        derivedAmbientPushforwardFunctor A :=
  Functor.whiskerRight
      (Functor.mapHomotopyCategoryPlusNatTrans (zariskiDirectImageToAmbient A))
      DerivedCategory.Plus.Qh ≫
    Functor.whiskerRight
      (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl _)).inv DerivedCategory.Plus.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (abelianAmbientRestriction A).mapHomotopyCategoryPlus
      (ambientPushforward A).rightDerivedFunctorPlusUnith ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (derivedAmbientRestrictionFactorsh A).inv
      (derivedAmbientPushforwardFunctor A) ≫
    (Functor.associator _ _ _).hom

/-- The components of `zariskiDirectImageToAmbientComparison`. -/
theorem zariskiDirectImageToAmbientComparison_app
    (K : HomotopyCategory.Plus (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})) :
    (zariskiDirectImageToAmbientComparison A).app K =
      DerivedCategory.Plus.Qh.map
          ((Functor.mapHomotopyCategoryPlusNatTrans (zariskiDirectImageToAmbient A)).app K) ≫
        DerivedCategory.Plus.Qh.map
          ((Functor.mapHomotopyCategoryPlusCompIso
            (Iso.refl (abelianAmbientRestriction A ⋙ ambientPushforward A))).inv.app K) ≫
        (ambientPushforward A).rightDerivedFunctorPlusUnith.app
          ((abelianAmbientRestriction A).mapHomotopyCategoryPlus.obj K) ≫
        (derivedAmbientPushforwardFunctor A).map
          ((derivedAmbientRestrictionFactorsh A).inv.app K) := by
  simp only [zariskiDirectImageToAmbientComparison, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id]

/-- **The derived transformation `Ru_{X/S, *}K ⟶ Rh_*(K_T)`**, natural in the bounded below
complex `K` of abelian sheaves on `Cris(X/S)`: the derived functor of
`zariskiDirectImageToAmbient`, the unique natural transformation out of the right derived functor
`Ru_{X/S, *}` restricting to `zariskiDirectImageToAmbientComparison` on complexes
(`derivedZariskiDirectImageToAmbient_fac_app`).  Its source is
`derivedZariskiDirectImageFunctor S`, unfolded. -/
def derivedZariskiDirectImageToAmbient :
    (zariskiDirectImage S).rightDerivedFunctorPlus ⟶
      derivedAmbientRestriction A ⋙ derivedAmbientPushforwardFunctor A :=
  (zariskiDirectImage S).rightDerivedFunctorPlus.rightDerivedDesc
    (zariskiDirectImage S).rightDerivedFunctorPlusUnith (HomotopyCategory.Plus.quasiIso _) _
    (zariskiDirectImageToAmbientComparison A)

/-- **The derived transformation is the derived functor of the termwise one**: its composite with
the canonical map `u_{X/S, *}K ⟶ Ru_{X/S, *}K` is `zariskiDirectImageToAmbientComparison`. -/
@[reassoc]
theorem derivedZariskiDirectImageToAmbient_fac_app
    (K : HomotopyCategory.Plus (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})) :
    (zariskiDirectImage S).rightDerivedFunctorPlusUnith.app K ≫
        (derivedZariskiDirectImageToAmbient A).app (DerivedCategory.Plus.Qh.obj K) =
      (zariskiDirectImageToAmbientComparison A).app K :=
  NatTrans.congr_app (Functor.rightDerived_fac _ _ _ _ _) K

variable [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]

/-- **`RΓ(X_Zar, Rh_* -) ≅ RΓ(T, -)`**: the composition of derived functors, `h_*` preserving
injective objects, followed by the isomorphism of derived functors induced by
`Γ(X_Zar, h_* -) ≅ Γ(T, -)`. -/
def derivedAmbientPushforwardGlobalSectionsIso :
    derivedAmbientPushforwardFunctor A ⋙ derivedZariskiGlobalSectionsFunctor S ≅
      derivedAmbientGlobalSectionsFunctor A :=
  (Functor.rightDerivedFunctorPlusCompIso (ambientPushforward A)
      (zariskiGlobalSections S)).symm ≪≫
    Functor.rightDerivedFunctorPlusNatIso (ambientPushforwardGlobalSectionsIso A)

/-- **The derived comparison on a bounded below complex.**  The canonical map
`Γ(Cris(X/S), K) ⟶ RΓ(Cris(X/S), K)`, followed by `RΓ(Cris(X/S), K) ≅ RΓ(X_Zar, Ru_{X/S, *}K)`,
`RΓ(X_Zar, -)` of the derived transformation, and `RΓ(X_Zar, Rh_*(K_T)) ≅ RΓ(T, K_T)`, is
`globalSectionsToAmbientComparison`. -/
theorem derivedZariskiDirectImageToAmbient_globalSections_fac
    (K : HomotopyCategory.Plus (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})) :
    (globalSections S).rightDerivedFunctorPlusUnith.app K ≫
        (derivedGlobalSectionsIsoDerivedZariskiDirectImage S).hom.app
          (DerivedCategory.Plus.Qh.obj K) ≫
        (derivedZariskiGlobalSectionsFunctor S).map
          ((derivedZariskiDirectImageToAmbient A).app (DerivedCategory.Plus.Qh.obj K)) ≫
        (derivedAmbientPushforwardGlobalSectionsIso A).hom.app
          ((derivedAmbientRestriction A).obj (DerivedCategory.Plus.Qh.obj K)) =
      (globalSectionsToAmbientComparison A).app K := by
  let M := (abelianAmbientRestriction A).mapHomotopyCategoryPlus.obj K
  have h1 := Functor.rightDerivedFunctorPlusNatIso_inv_fac_app
    (zariskiGlobalSectionsDirectImageIso S) K
  have h2 := Functor.rightDerivedFunctorPlusComp_fac_app (zariskiDirectImage S)
    (zariskiGlobalSections S) K
  have h3 := derivedZariskiDirectImageToAmbient_fac_app A K
  rw [zariskiDirectImageToAmbientComparison_app] at h3
  have h4 := (zariskiGlobalSections S).rightDerivedFunctorPlusUnith.naturality
    ((Functor.mapHomotopyCategoryPlusNatTrans (zariskiDirectImageToAmbient A)).app K)
  simp only [Functor.comp_map] at h4
  have h4' := (zariskiGlobalSections S).rightDerivedFunctorPlusUnith.naturality
    ((Functor.mapHomotopyCategoryPlusCompIso
      (Iso.refl (abelianAmbientRestriction A ⋙ ambientPushforward A))).inv.app K)
  simp only [Functor.comp_map] at h4'
  have h5 := Functor.rightDerivedFunctorPlusComp_fac_app (ambientPushforward A)
    (zariskiGlobalSections S) M
  have h5' : (zariskiGlobalSections S).rightDerivedFunctorPlusUnith.app
        ((ambientPushforward A).mapHomotopyCategoryPlus.obj M) ≫
      (zariskiGlobalSections S).rightDerivedFunctorPlus.map
        ((ambientPushforward A).rightDerivedFunctorPlusUnith.app M) =
      DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusCompIso
          (Iso.refl (ambientPushforward A ⋙ zariskiGlobalSections S))).hom.app M) ≫
        (ambientPushforward A ⋙ zariskiGlobalSections S).rightDerivedFunctorPlusUnith.app M ≫
          (Functor.rightDerivedFunctorPlusComp (ambientPushforward A) (zariskiGlobalSections S)).app
            (DerivedCategory.Plus.Qh.obj M) := by
    rw [h5, ← DerivedCategory.Plus.Qh.map_comp_assoc, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have h6 := Functor.rightDerivedFunctorPlusNatIso_hom_fac_app
    (ambientPushforwardGlobalSectionsIso A) M
  have h7a := (Functor.rightDerivedFunctorPlusCompIso (ambientPushforward A)
    (zariskiGlobalSections S)).inv.naturality ((derivedAmbientRestrictionFactorsh A).inv.app K)
  have h7b := (Functor.rightDerivedFunctorPlusNatIso
    (ambientPushforwardGlobalSectionsIso A)).hom.naturality
      ((derivedAmbientRestrictionFactorsh A).inv.app K)
  simp only [Functor.comp_map, Functor.comp_obj] at h7a h7b
  have h8 : (Functor.mapHomotopyCategoryPlusNatIso
        (zariskiGlobalSectionsDirectImageIso S)).inv.app K ≫
      (Functor.mapHomotopyCategoryPlusCompIso
        (Iso.refl (zariskiDirectImage S ⋙ zariskiGlobalSections S))).inv.app K ≫
      (zariskiGlobalSections S).mapHomotopyCategoryPlus.map
        ((Functor.mapHomotopyCategoryPlusNatTrans (zariskiDirectImageToAmbient A)).app K) ≫
      (zariskiGlobalSections S).mapHomotopyCategoryPlus.map
        ((Functor.mapHomotopyCategoryPlusCompIso
          (Iso.refl (abelianAmbientRestriction A ⋙ ambientPushforward A))).inv.app K) ≫
      (Functor.mapHomotopyCategoryPlusCompIso
        (Iso.refl (ambientPushforward A ⋙ zariskiGlobalSections S))).hom.app M ≫
      (Functor.mapHomotopyCategoryPlusNatIso (ambientPushforwardGlobalSectionsIso A)).hom.app M =
      (Functor.mapHomotopyCategoryPlusNatTrans (globalSectionsToAmbient A)).app K ≫
        (Functor.mapHomotopyCategoryPlusCompIso
          (Iso.refl (abelianAmbientRestriction A ⋙ ambientGlobalSections A))).inv.app K := by
    rw [Stacks.Cohomology.BaseChange.mapHomotopyCategoryPlusCompIso_refl_inv_comp,
      ← CategoryTheory.Functor.map_comp_assoc,
      Stacks.Cohomology.BaseChange.mapHomotopyCategoryPlusCompIso_refl_comp_inv,
      Stacks.Cohomology.BaseChange.mapHomotopyCategoryPlusCompIso_refl_hom_comp,
      Stacks.Cohomology.BaseChange.mapHomotopyCategoryPlusCompIso_refl_comp_inv]
    exact mapHomotopyCategoryPlus_zariskiDirectImageToAmbient_globalSections A K
  have hQ := congrArg (fun f => DerivedCategory.Plus.Qh.map f) h8
  simp only [CategoryTheory.Functor.map_comp] at hQ
  have h9 : ∀ {Z} (h : _ ⟶ Z),
      (Functor.rightDerivedFunctorPlusComp (ambientPushforward A) (zariskiGlobalSections S)).app
          (DerivedCategory.Plus.Qh.obj M) ≫
        (Functor.rightDerivedFunctorPlusCompIso (ambientPushforward A)
          (zariskiGlobalSections S)).inv.app (DerivedCategory.Plus.Qh.obj M) ≫ h = h :=
    fun h => Iso.hom_inv_id_app_assoc
      (Functor.rightDerivedFunctorPlusCompIso (ambientPushforward A) (zariskiGlobalSections S)) _ h
  have hR : (globalSectionsToAmbientComparison A).app K =
      DerivedCategory.Plus.Qh.map
          ((Functor.mapHomotopyCategoryPlusNatTrans (globalSectionsToAmbient A)).app K) ≫
        DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusCompIso
          (Iso.refl (abelianAmbientRestriction A ⋙ ambientGlobalSections A))).inv.app K) ≫
        (ambientGlobalSections A).rightDerivedFunctorPlusUnith.app M ≫
        (ambientGlobalSections A).rightDerivedFunctorPlus.map
          ((derivedAmbientRestrictionFactorsh A).inv.app K) := by
    simp only [globalSectionsToAmbientComparison, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp]
    exact congrArg (_ ≫ ·) (congrArg (_ ≫ ·) (congrArg (_ ≫ ·) (Category.comp_id _)))
  rw [hR]
  delta derivedGlobalSectionsFunctor derivedZariskiDirectImageFunctor
    derivedZariskiGlobalSectionsFunctor derivedAmbientGlobalSectionsFunctor
    derivedGlobalSectionsIsoDerivedZariskiDirectImage derivedAmbientPushforwardGlobalSectionsIso
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc,
    Functor.rightDerivedFunctorPlusCompIso_hom]
  rw [reassoc_of% h1, reassoc_of% h2,
    ← CategoryTheory.Functor.map_comp_assoc (zariskiGlobalSections S).rightDerivedFunctorPlus, h3]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← reassoc_of% h4, ← reassoc_of% h4', reassoc_of% h5', reassoc_of% h7a, h7b, h9,
    reassoc_of% h6]
  rw [reassoc_of% hQ]

/-- **On derived global sections, the derived transformation `Ru_{X/S, *}K ⟶ Rh_*(K_T)` is the
restriction `RΓ(Cris(X/S), K) ⟶ RΓ(T, K_T)` of [Stacks, Equation 07LP]**: for every bounded below
complex `K` of abelian sheaves on `Cris(X/S)`, the composite of
`RΓ(Cris(X/S), K) ≅ RΓ(X_Zar, Ru_{X/S, *}K)`, of `RΓ(X_Zar, -)` applied to
`derivedZariskiDirectImageToAmbient`, and of `RΓ(X_Zar, Rh_*(K_T)) ≅ RΓ(T, K_T)` is
`derivedGlobalSectionsToAmbient A` at `K`. -/
theorem derivedZariskiDirectImageToAmbient_globalSections
    (K : DerivedCategory.Plus (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})) :
    (derivedGlobalSectionsIsoDerivedZariskiDirectImage S).hom.app K ≫
        (derivedZariskiGlobalSectionsFunctor S).map
          ((derivedZariskiDirectImageToAmbient A).app K) ≫
        (derivedAmbientPushforwardGlobalSectionsIso A).hom.app
          ((derivedAmbientRestriction A).obj K) =
      (derivedGlobalSectionsToAmbient A).app K := by
  have h := derivedGlobalSectionsToAmbient_unique A
    ((derivedGlobalSectionsIsoDerivedZariskiDirectImage S).hom ≫
      Functor.whiskerRight (derivedZariskiDirectImageToAmbient A)
        (derivedZariskiGlobalSectionsFunctor S) ≫
      Functor.whiskerLeft (derivedAmbientRestriction A)
        (derivedAmbientPushforwardGlobalSectionsIso A).hom)
    (NatTrans.ext (funext fun L => derivedZariskiDirectImageToAmbient_globalSections_fac A L))
  exact NatTrans.congr_app h K

end Derived

end CrystallineThickening

end Crystalline.GlobalCrystallineSituation.SmallSite

end
