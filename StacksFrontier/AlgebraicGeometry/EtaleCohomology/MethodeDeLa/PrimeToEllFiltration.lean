module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MethodeDeLa.ZModGeometricFibre
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MethodeDeLa.PrimeToEllCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.BaseChangeRepresentable
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.StalksTestMaps
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleConnectedObjects
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategory.OpenSubgroups

/-!
# Tag 0A3R: filtering a locally constant `F_ℓ`-sheaf after a cover of degree prime to `ℓ`

Let `S` be a connected scheme, `ℓ` a prime and `F` a finite type locally constant sheaf of
`F_ℓ`-vector spaces on `S_étale`. There is a finite étale `f : T → S` of degree prime to `ℓ` such
that `f⁻¹F` has a finite filtration with successive quotients `Z/ℓZ_T`.

## Main results

* `Stacks.EtaleCohomology.exists_primeToEll_finiteEtale_relSeries_constantRankOneStep`:
  **Tag 0A3R**, with no hypothesis beyond the source's.

## Implementation notes

The proof is the one of the source, run on geometric fibres instead of on a dictionary with
representations. The underlying sheaf of sets of `F` is represented by a finite étale cover `X`
of `S` (Tag 03RV), on whose geometric fibre at `s̄` the fundamental group `π₁(S, s̄)` acts through
a finite group `G`. The preimage `U` of an `ℓ`-Sylow subgroup of `G` is an open subgroup, and the
cover `T` attached to `π₁(S, s̄)/U` (Tag 0BND) is connected of degree `[G : H]`. The inverse image
of `F` on `T` is represented by `X ×_S T`, on whose fibre `π₁(T, t̄)` acts through the stabiliser
of the base point of the fibre of `T`, contained in `U`, hence through an `ℓ`-group; and a finite
type locally constant sheaf of `F_ℓ`-vector spaces with `ℓ`-group monodromy is a successive
extension of copies of `Z/ℓZ`
(`Stacks.EtaleCohomology.exists_relSeries_constantRankOneStep_of_monodromy`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.ConstantSheaf

universe u

namespace Stacks.EtaleCohomology

variable (ℓ : ℕ) (B : BigEtaleSite.{u})

/-- The underlying sheaf of sets of a sheaf of `F_ℓ`-vector spaces, transported to the
size-bounded small étale site. -/
abbrev zmodRawSetSheaf (X : B.Scheme)
    (G : Sheaf X.1.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ))) :
    Sheaf (SmallEtale.topology B X.1 X.2) (Type (u + 1)) :=
  (sheafCompose _ (forget AddCommGrpCat.{u + 1})).obj
    ((toBoundedSite B X AddCommGrpCat.{u + 1}).obj ((forgetZMod ℓ X.1).obj G))

/-- The transported underlying sheaf of sets is the transport of the underlying sheaf of sets. -/
def zmodRawSetSheafIso (X : B.Scheme)
    (G : Sheaf X.1.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ))) :
    zmodRawSetSheaf ℓ B X G ≅ (toBoundedSite B X (Type (u + 1))).obj
      ((sheafCompose _ (forget (ModuleCat.{u + 1} (ZMod ℓ)))).obj G) :=
  eqToIso (congrArg (toBoundedSite B X (Type (u + 1))).obj
    (sheafCompose_forget₂_forget.{u, u + 1} X.1.smallEtaleTopology (ZMod ℓ) G))

variable {B} {XS XT : B.Scheme} (fB : XT ⟶ XS) [Etale (B.inclusion.map fB)]

/-- **Inverse image along an étale morphism commutes with the transported underlying sheaf of
sets.** For an étale `f : T ⟶ S`, the transported underlying sheaf of sets of `f⁻¹F` is the
inverse image, on the size-bounded small étale sites, of that of `F`: on Mathlib's sites inverse
image along an étale morphism is restriction, which commutes with forgetting the module
structure, and inverse image commutes with the passage to the size-bounded sites. -/
def zmodRawSetSheafPullbackIso (F : Sheaf XS.1.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ))) :
    zmodRawSetSheaf ℓ B XT ((smallEtalePullbackZMod.{0} ℓ (B.inclusion.map fB)).obj F) ≅
      (smallEtaleSheafPullbackType B fB).obj (zmodRawSetSheaf ℓ B XS F) := by
  let f := B.inclusion.map fB
  let W := (sheafCompose _ (forget (ModuleCat.{u + 1} (ZMod ℓ)))).obj F
  have : HasLimitsOfSize.{u, u} (Type (u + 1)) := inferInstance
  let ES := SmallEtale.sheafEquiv B XS.1 XS.2 (Type (u + 1))
  let ET := SmallEtale.sheafEquiv B XT.1 XT.2 (Type (u + 1))
  let LU := (Stacks.EtaleCohomology.smallEtaleBaseChange f).sheafPullback (Type (u + 1))
    XS.1.smallEtaleTopology XT.1.smallEtaleTopology
  let LB := smallEtaleSheafPullbackType B fB
  let c := SmallEtale.sheafEquivPullbackBaseChangeIso B fB (Type (u + 1))
    ((Stacks.EtaleCohomology.smallEtaleBaseChange f).sheafAdjunctionContinuous (Type (u + 1))
      XS.1.smallEtaleTopology XT.1.smallEtaleTopology)
    ((AlgebraicGeometry.smallEtaleBaseChange B fB).sheafAdjunctionContinuous (Type (u + 1))
      (SmallEtale.topology B XS.1 XS.2) (SmallEtale.topology B XT.1 XT.2))
  let e₁ : zmodRawSetSheaf ℓ B XT ((smallEtalePullbackZMod.{0} ℓ f).obj F) ≅
      (toBoundedSite B XT (Type (u + 1))).obj (LU.obj W) :=
    zmodRawSetSheafIso ℓ B XT _ ≪≫
      (toBoundedSite B XT (Type (u + 1))).mapIso
        ((sheafCompose _ (forget (ModuleCat.{u + 1} (ZMod ℓ)))).mapIso
          ((Scheme.Etale.sheafPullbackIsoRestrict f (ModuleCat.{u + 1} (ZMod ℓ))).app F) ≪≫
        ((Scheme.Etale.sheafPullbackIsoRestrict f (Type (u + 1))).app W).symm)
  let e₂ : (toBoundedSite B XT (Type (u + 1))).obj (LU.obj W) ≅
      LB.obj ((toBoundedSite B XS (Type (u + 1))).obj W) :=
    (toBoundedSite B XT (Type (u + 1))).mapIso (LU.mapIso (ES.counitIso.app W).symm) ≪≫
      (toBoundedSite B XT (Type (u + 1))).mapIso (c.app (ES.inverse.obj W)) ≪≫
      (ET.unitIso.app _).symm
  exact e₁ ≪≫ e₂ ≪≫ LB.mapIso (zmodRawSetSheafIso ℓ B XS F).symm

variable {ℓ} in
/-- **Finite type local constancy is detected on the transported underlying sheaf of sets.** If
the transported underlying sheaf of sets of a sheaf `G` of `F_ℓ`-vector spaces is finite locally
constant, then `G` is a finite type locally constant sheaf of `F_ℓ`-vector spaces. -/
theorem zmodFiniteTypeLocallyConstant_of_rawSetSheaf [NeZero ℓ] (X : B.Scheme)
    (G : Sheaf X.1.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ)))
    (hG : IsFiniteLocallyConstant (SmallEtale.topology B X.1 X.2) (zmodRawSetSheaf ℓ B X G)) :
    zmodFiniteTypeLocallyConstant ℓ X.1 G := by
  have h₁ : IsFiniteLocallyConstant (SmallEtale.topology B X.1 X.2)
      ((toBoundedSite B X (Type (u + 1))).obj
        ((sheafCompose _ (forget (ModuleCat.{u + 1} (ZMod ℓ)))).obj G)) :=
    (isFiniteLocallyConstantSetSheaf.{u, u + 1, u + 1} _).prop_of_iso
      (zmodRawSetSheafIso ℓ B X G) hG
  have h₂ := (SmallEtale.isFiniteLocallyConstant_iff_toEtaleSite B X.1 X.2 _).mpr h₁
  have h₃ := isFiniteLocallyConstant_moduleSheaf_of_forget.{u, u + 1} X.1.smallEtaleTopology
    (ZMod ℓ) G h₂
  intro U
  obtain ⟨I, V, f, hcov, htriv⟩ := h₃.exists_finite_cover U
  refine ⟨I, V, f, hcov, fun i ↦ ?_⟩
  obtain ⟨E, hE, he⟩ := htriv i
  exact ⟨E, (Stacks.GroupCohomology.moduleCat_isFG_iff_finite (ZMod ℓ) E).mpr hE, he⟩

variable [NeZero ℓ] (F : Sheaf XS.1.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ)))
  (hF : zmodFiniteTypeLocallyConstant ℓ XS.1 F)

/-- The finite object of the small étale site of `S` representing the transported underlying
sheaf of sets of `F`. -/
abbrev zmodRepresentingObject :
    (finiteSmallEtaleObjects B XS).FullSubcategory :=
  (finiteSmallEtaleToFiniteLocallyConstant B XS).asEquivalence.inverse.obj
    (zmodFibreSetSheaf ℓ B XS ⟨F, hF⟩)

/-- The transported underlying sheaf of sets of `f⁻¹F` is represented by the base change of the
cover representing that of `F`. -/
def zmodRawSetSheafPullbackYonedaIso :
    zmodRawSetSheaf ℓ B XT ((smallEtalePullbackZMod.{0} ℓ (B.inclusion.map fB)).obj F) ≅
      ((finiteSmallEtaleToFiniteLocallyConstant B XT).obj
        ((finiteSmallEtaleBaseChange B fB).obj (zmodRepresentingObject ℓ F hF))).obj :=
  zmodRawSetSheafPullbackIso ℓ fB F ≪≫
    ((ObjectProperty.ι _).mapIso ((finiteLocallyConstantSheafPullback B fB).mapIso
      ((finiteSmallEtaleToFiniteLocallyConstant B XS).asEquivalence.counitIso.app
        (zmodFibreSetSheaf ℓ B XS ⟨F, hF⟩)).symm ≪≫
      (finiteSmallEtaleToFiniteLocallyConstantBaseChangeIso B fB).app _))

include hF in
/-- **The inverse image of a finite type locally constant sheaf of `F_ℓ`-vector spaces along an
étale morphism is finite type locally constant.** -/
theorem zmodFiniteTypeLocallyConstant_pullback :
    zmodFiniteTypeLocallyConstant ℓ XT.1
      ((smallEtalePullbackZMod.{0} ℓ (B.inclusion.map fB)).obj F) :=
  zmodFiniteTypeLocallyConstant_of_rawSetSheaf XT _
    ((isFiniteLocallyConstantSetSheaf.{u, u + 1, u + 1} _).prop_of_iso
      (zmodRawSetSheafPullbackYonedaIso ℓ fB F hF).symm
      ((finiteSmallEtaleToFiniteLocallyConstant B XT).obj
        ((finiteSmallEtaleBaseChange B fB).obj (zmodRepresentingObject ℓ F hF))).property)

/-- **The cover representing the inverse image is the base change of the cover representing
`F`.** -/
def representingCoverPullbackIso :
    (representingCover B XT).obj (zmodFibreSetSheaf ℓ B XT
        ⟨_, zmodFiniteTypeLocallyConstant_pullback ℓ fB F hF⟩) ≅
      (finiteEtaleBaseChange (B.inclusion.map fB)).obj
        ((representingCover B XS).obj (zmodFibreSetSheaf ℓ B XS ⟨F, hF⟩)) :=
  (representingCover B XT).mapIso
      (ObjectProperty.isoMk _ (zmodRawSetSheafPullbackYonedaIso ℓ fB F hF)) ≪≫
    (finiteEtaleSiteEquivalence B XT).functor.mapIso
      ((finiteSmallEtaleToFiniteLocallyConstant B XT).asEquivalence.unitIso.app
        ((finiteSmallEtaleBaseChange B fB).obj (zmodRepresentingObject ℓ F hF))).symm ≪≫
    MorphismProperty.Over.isoMk
      (PreservesPullback.iso B.inclusion (zmodRepresentingObject ℓ F hF).1.obj.hom fB)
      (PreservesPullback.iso_hom_snd B.inclusion _ fB)

/-! ### Monodromy along a finite étale cover -/

/-- **A power of an element of `π₁(X, x)` acts trivially on the fibre of a base change as soon as
the same power of its image acts trivially on the fibre of the cover.** The projection from the
fibre of `V ×_Y X` to the fibre of `V` is bijective and intertwines the two actions
(Tag 0BND (3)). -/
theorem pow_app_finiteEtaleBaseChange_eq_self {X Y : Scheme.{u}} [ConnectedSpace X]
    [ConnectedSpace Y] (f : X ⟶ Y) (x : GeometricPoint X) (V : FiniteEtaleOver Y)
    (σ : EtaleFundamentalGroup X x) (n : ℕ)
    (h : ∀ q : (finiteEtaleFiberFunctor (x.map f)).obj V,
      (((etaleFundamentalGroupMap f x σ) ^ n).app V).hom q = q)
    (p : (finiteEtaleFiberFunctor x).obj ((finiteEtaleBaseChange f).obj V)) :
    ((σ ^ n).app ((finiteEtaleBaseChange f).obj V)).hom p = p := by
  apply (finiteEtaleFiberProjectionEquiv f x V).injective
  show finiteEtaleFiberProjection f x V _ = finiteEtaleFiberProjection f x V p
  rw [etaleFundamentalGroupMap_finiteEtaleFiberProjection, map_pow]
  exact h _

/-- **The image of `π₁(X, x̄)` fixes the points of a fibre coming from `X`.** For a morphism
`f : X ⟶ Y` of connected schemes, a finite étale cover `V` of `Y` and a lift `i : X ⟶ V` of `f`,
the image in `π₁(Y, f(x̄))` of every element of `π₁(X, x̄)` fixes the point `i(x̄)` of the
geometric fibre of `V`: that point is the projection of a point of the fibre of `V ×_Y X` coming
from the terminal cover of `X`, which every natural automorphism fixes. -/
theorem etaleFundamentalGroupMap_app_lift {X Y : Scheme.{u}} [ConnectedSpace X]
    [ConnectedSpace Y] (f : X ⟶ Y) (x : GeometricPoint X) (V : FiniteEtaleOver Y)
    (i : X ⟶ V.left) (hi : i ≫ V.hom = f) (σ : EtaleFundamentalGroup X x) :
    ((etaleFundamentalGroupMap f x σ).app V).hom
        ⟨x.hom ≫ i, by rw [Category.assoc, hi]; rfl⟩ =
      ⟨x.hom ≫ i, by rw [Category.assoc, hi]; rfl⟩ := by
  let W := (finiteEtaleBaseChange f).obj V
  let Δ : terminalCover X ⟶ W :=
    MorphismProperty.Over.homMk (pullback.lift i (𝟙 X) (hi.trans (Category.id_comp f).symm))
      (pullback.lift_snd _ _ _)
  let pt : (finiteEtaleFiberFunctor x).obj (terminalCover X) := ⟨x.hom, Category.comp_id _⟩
  let p₀ := (finiteEtaleFiberFunctor x).map Δ pt
  have hp₀ : finiteEtaleFiberProjection f x V p₀ =
      ⟨x.hom ≫ i, by rw [Category.assoc, hi]; rfl⟩ :=
    Subtype.ext ((Category.assoc _ _ _).trans (congrArg (x.hom ≫ ·) (pullback.lift_fst _ _ _)))
  have hfix : (σ.app W).hom p₀ = p₀ := by
    have hn := congrArg (fun g ↦ g pt) (σ.hom.naturality Δ)
    simp only [types_comp_apply] at hn
    refine hn.trans ?_
    congr 1
    exact Subsingleton.elim (α := (finiteEtaleFiberFunctor x).obj (terminalCover X)) _ _
  rw [← hp₀, ← etaleFundamentalGroupMap_finiteEtaleFiberProjection, hfix]

/-- **The kernel of the monodromy action on a geometric fibre is open.** The kernel of the action
of `π₁(S, s̄)` on the geometric fibre of a finite étale cover is the intersection of the finitely
many stabilisers of the points of the fibre, each of which is open. -/
private theorem isOpen_ker_toPermHom_finiteEtaleFiber {S : Scheme.{u}} [ConnectedSpace S]
    (s : GeometricPoint S) (X : FiniteEtaleOver S) :
    IsOpen (((MulAction.toPermHom (EtaleFundamentalGroup S s)
      ((finiteEtaleFiberFunctor s).obj X)).ker : Subgroup (EtaleFundamentalGroup S s)) :
        Set (EtaleFundamentalGroup S s)) := by
  have : Finite ((finiteEtaleFiberFunctor s).obj X) := finite_finiteEtaleFiber s X
  have : (((MulAction.toPermHom (EtaleFundamentalGroup S s)
      ((finiteEtaleFiberFunctor s).obj X)).ker : Subgroup (EtaleFundamentalGroup S s)) :
        Set (EtaleFundamentalGroup S s)) =
      ⋂ y : (finiteEtaleFiberFunctor s).obj X,
        ((MulAction.stabilizer (EtaleFundamentalGroup S s) y :
          Subgroup (EtaleFundamentalGroup S s)) : Set (EtaleFundamentalGroup S s)) := by
    ext τ
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, MulAction.mem_stabilizer_iff]
    exact ⟨fun h y ↦ congrArg (fun g : Equiv.Perm _ ↦ g y) h, fun h ↦ Equiv.ext h⟩
  rw [this]
  exact isOpen_iInter_of_finite fun y ↦
    EtaleFundamentalGroup.isOpen_coe_of_isOpenSubgroup ⟨X, y, rfl⟩

/-! ### Tag 0A3R -/

variable {ℓ} in
omit [NeZero ℓ] in
/-- **The filtration over a connected finite étale cover with `ℓ`-group monodromy.** Let `T` be a
connected finite étale cover of `S` and `y₀` a point of its geometric fibre at `s̄`. If every
element of `π₁(S, s̄)` fixing `y₀` has an `ℓ`-power acting trivially on the geometric fibre of the
cover representing `F`, then the inverse image of `F` on `T` is a successive extension of copies
of `Z/ℓZ`. The point `y₀` is a geometric point `t̄` of `T` lying over `s̄`, and the image of
`π₁(T, t̄)` in `π₁(S, s̄)` fixes it. -/
theorem exists_relSeries_constantRankOneStep_of_stabilizer (hℓ : ℓ.Prime) (XS : B.Scheme)
    [ConnectedSpace XS.1] (F : Sheaf XS.1.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ)))
    (hF : have : NeZero ℓ := ⟨hℓ.ne_zero⟩; zmodFiniteTypeLocallyConstant ℓ XS.1 F)
    (T : FiniteEtaleOver XS.1) [ConnectedSpace T.left] (t : GeometricPoint T.left)
    (hfix : have : NeZero ℓ := ⟨hℓ.ne_zero⟩
      ∀ τ : EtaleFundamentalGroup XS.1 (t.map T.hom),
        (τ.app T).hom ⟨t.hom, rfl⟩ = ⟨t.hom, rfl⟩ → ∃ k : ℕ,
          ∀ q : (finiteEtaleFiberFunctor (t.map T.hom)).obj
            ((representingCover B XS).obj (zmodFibreSetSheaf ℓ B XS ⟨F, hF⟩)),
            ((τ ^ (ℓ ^ k)).app _).hom q = q) :
    ∃ X : RelSeries (ConstantRankOneStep.{0} ℓ ((smallEtalePullbackZMod.{0} ℓ T.hom).obj F)),
      IsZero (Subobject.underlying.obj X.head) ∧ IsIso X.last.arrow := by
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have : ConnectedSpace ((𝟭 Scheme).obj T.left) := ‹ConnectedSpace T.left›
  have : ConnectedSpace ((Functor.fromPUnit XS.1).obj T.right) := ‹ConnectedSpace XS.1›
  let XT : B.Scheme := ⟨T.left, finiteEtale_size_lt T⟩
  let fB : XT ⟶ XS := ObjectProperty.homMk T.hom
  have : Etale (B.inclusion.map fB) := T.prop.2
  refine exists_relSeries_constantRankOneStep_of_monodromy (B := B) (X := XT) (x := t) hℓ _
    (zmodFiniteTypeLocallyConstant_pullback ℓ fB F hF) _
    (representingCoverPullbackIso ℓ fB F hF) fun σ ↦ ?_
  have h₁ := etaleFundamentalGroupMap_app_lift (X := T.left) (Y := XS.1) T.hom t T (𝟙 T.left)
    (Category.id_comp _) σ
  have e : (⟨t.hom ≫ 𝟙 T.left, by rw [Category.assoc, Category.id_comp]; rfl⟩ :
      (finiteEtaleFiberFunctor (t.map T.hom)).obj T) = ⟨t.hom, rfl⟩ :=
    Subtype.ext (Category.comp_id _)
  rw [e] at h₁
  obtain ⟨k, hk⟩ := hfix _ h₁
  exact ⟨k, pow_app_finiteEtaleBaseChange_eq_self T.hom t _ σ (ℓ ^ k) hk⟩

variable {ℓ} in
omit [NeZero ℓ] in
/-- **The filtration over a connected finite étale cover, from a point of its fibre.** The form
of `exists_relSeries_constantRankOneStep_of_stabilizer` in which the point `y₀` is given in the
geometric fibre of `T` at `s̄`, rather than as a geometric point of `T`. -/
private theorem exists_relSeries_constantRankOneStep_of_fiberStabilizer (hℓ : ℓ.Prime)
    (XS : B.Scheme) [ConnectedSpace XS.1]
    (F : Sheaf XS.1.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ)))
    (hF : have : NeZero ℓ := ⟨hℓ.ne_zero⟩; zmodFiniteTypeLocallyConstant ℓ XS.1 F)
    (T : FiniteEtaleOver XS.1) [ConnectedSpace T.left] (s : GeometricPoint XS.1)
    (y₀ : (finiteEtaleFiberFunctor s).obj T)
    (hfix : have : NeZero ℓ := ⟨hℓ.ne_zero⟩
      ∀ τ : EtaleFundamentalGroup XS.1 s, (τ.app T).hom y₀ = y₀ → ∃ k : ℕ,
        ∀ q : (finiteEtaleFiberFunctor s).obj
          ((representingCover B XS).obj (zmodFibreSetSheaf ℓ B XS ⟨F, hF⟩)),
          ((τ ^ (ℓ ^ k)).app _).hom q = q) :
    ∃ X : RelSeries (ConstantRankOneStep.{0} ℓ ((smallEtalePullbackZMod.{0} ℓ T.hom).obj F)),
      IsZero (Subobject.underlying.obj X.head) ∧ IsIso X.last.arrow := by
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  let t : GeometricPoint T.left := { residueField := s.residueField, hom := y₀.1 }
  have hts : s = t.map T.hom := by
    show s = GeometricPoint.mk s.residueField (y₀.1 ≫ T.hom)
    rw [y₀.2]
    rfl
  have key : ∀ (s' : GeometricPoint XS.1) (h : s = s') (τ : EtaleFundamentalGroup XS.1 s'),
      (τ.app T).hom (h ▸ y₀) = h ▸ y₀ → ∃ k : ℕ,
        ∀ q : (finiteEtaleFiberFunctor s').obj
          ((representingCover B XS).obj (zmodFibreSetSheaf ℓ B XS ⟨F, hF⟩)),
          ((τ ^ (ℓ ^ k)).app _).hom q = q := by
    intro s' h
    subst h
    exact hfix
  have hval : ∀ (s₁ s₂ : GeometricPoint XS.1) (h : s₁ = s₂)
      (y : (finiteEtaleFiberFunctor s₁).obj T),
      HEq (h ▸ y : (finiteEtaleFiberFunctor s₂).obj T).1 y.1 := by
    intro s₁ s₂ h y
    subst h
    rfl
  have hy : (hts ▸ y₀ : (finiteEtaleFiberFunctor (t.map T.hom)).obj T) = ⟨t.hom, rfl⟩ :=
    Subtype.ext (eq_of_heq (hval _ _ hts y₀))
  have key' := key _ hts
  rw [hy] at key'
  exact exists_relSeries_constantRankOneStep_of_stabilizer hℓ XS F hF T t key'

variable {ℓ} in
omit [NeZero ℓ] in
/-- **The filtration over the cover attached to an open subgroup.** Let `U` be an open subgroup
of `π₁(S, s̄)` of index prime to `ℓ`, each of whose elements has an `ℓ`-power acting trivially on
the geometric fibre of the cover representing `F`. Then the finite étale cover `T` of `S`
attached to `π₁(S, s̄)/U` is of degree prime to `ℓ`, and the inverse image of `F` on `T` is a
successive extension of copies of `Z/ℓZ`. -/
private theorem exists_primeToEll_finiteEtale_relSeries_of_openSubgroup (hℓ : ℓ.Prime)
    (XS : B.Scheme) [ConnectedSpace XS.1]
    (F : Sheaf XS.1.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ)))
    (hF : have : NeZero ℓ := ⟨hℓ.ne_zero⟩; zmodFiniteTypeLocallyConstant ℓ XS.1 F)
    (s : GeometricPoint XS.1) (U : OpenSubgroup (EtaleFundamentalGroup XS.1 s))
    (hU : ¬ ℓ ∣ U.toSubgroup.index)
    (hfix : have : NeZero ℓ := ⟨hℓ.ne_zero⟩
      ∀ σ ∈ U.toSubgroup, ∃ k : ℕ,
        ∀ q : (finiteEtaleFiberFunctor s).obj
          ((representingCover B XS).obj (zmodFibreSetSheaf ℓ B XS ⟨F, hF⟩)),
          ((σ ^ (ℓ ^ k)).app _).hom q = q) :
    ∃ (T : Scheme.{u}) (f : T ⟶ XS.1) (d : ℕ), IsFinite f ∧ Etale f ∧
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d ∧ ¬ ℓ ∣ d ∧
      ∃ X : RelSeries (ConstantRankOneStep.{0} ℓ ((smallEtalePullbackZMod.{0} ℓ f).obj F)),
        IsZero (Subobject.underlying.obj X.head) ∧ IsIso X.last.arrow := by
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  -- the cover `T` attached to `π₁(S, s̄)/U`
  obtain ⟨T, φ, hφ⟩ := exists_finiteEtaleOver_quotient_fiber_equiv s U
  set y₀ := φ.symm
    ((1 : EtaleFundamentalGroup XS.1 s) : EtaleFundamentalGroup XS.1 s ⧸ U.toSubgroup)
  have hφy₀ : φ y₀ = ((1 : EtaleFundamentalGroup XS.1 s) :
      EtaleFundamentalGroup XS.1 s ⧸ U.toSubgroup) := φ.apply_symm_apply _
  have htrans : ∀ z, ∃ σ : EtaleFundamentalGroup XS.1 s, σ • y₀ = z := by
    intro z
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (φ z)
    refine ⟨a, φ.injective ?_⟩
    rw [hφ, hφy₀, ← ha]
    show ((a * 1 : EtaleFundamentalGroup XS.1 s) :
      EtaleFundamentalGroup XS.1 s ⧸ U.toSubgroup) = _
    rw [mul_one]
  have hstab : ∀ σ : EtaleFundamentalGroup XS.1 s, σ • y₀ = y₀ → σ ∈ U.toSubgroup := by
    intro σ hσ
    have h1 : σ • φ y₀ = φ y₀ := by rw [← hφ, hσ]
    rw [hφy₀] at h1
    have h2 : ((σ * 1 : EtaleFundamentalGroup XS.1 s) :
        EtaleFundamentalGroup XS.1 s ⧸ U.toSubgroup) =
          ((1 : EtaleFundamentalGroup XS.1 s) : _) := h1
    rw [mul_one] at h2
    have h3 : σ⁻¹ * 1 ∈ U.toSubgroup := QuotientGroup.eq.mp h2
    rw [mul_one] at h3
    exact U.toSubgroup.inv_mem h3
  -- `T` is connected: `π₁(S, s̄)` acts transitively on its fibre
  have : ConnectedSpace T.left := AlgebraicGeometry.connectedSpace_left_of_exists_smul_eq htrans
  refine ⟨T.left, T.hom, Nat.card ((finiteEtaleFiberFunctor s).obj T), T.prop.1, T.prop.2,
    isFiniteLocallyFreeOfRank_natCard_finiteEtaleFiber s T, ?_,
    exists_relSeries_constantRankOneStep_of_fiberStabilizer hℓ XS F hF T s y₀
      fun τ hτ ↦ hfix τ (hstab τ hτ)⟩
  rwa [Nat.card_congr φ, ← Subgroup.index_eq_card]

/-- **Stacks Project, Tag 0A3R.** Let `S` be a connected scheme, `ℓ` a prime number and `F` a
finite type locally constant sheaf of `F_ℓ`-vector spaces on `S_étale`. Then there is a finite
étale morphism `f : T → S` of degree prime to `ℓ` such that `f⁻¹F` has a finite filtration
whose successive quotients are isomorphic to `Z/ℓZ_T`.

The filtration is a chain of subobjects of `f⁻¹F` running from the zero subobject to the whole
sheaf, each step having the constant sheaf `Z/ℓZ_T` as its quotient. -/
@[stacks 0A3R]
theorem exists_primeToEll_finiteEtale_relSeries_constantRankOneStep {ℓ : ℕ} (hℓ : ℓ.Prime)
    {S : Scheme.{u}} [ConnectedSpace S]
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ)))
    (hF : IsFiniteTypeLocallyConstant (ZMod ℓ) S.smallEtaleTopology F) :
    ∃ (T : Scheme.{u}) (f : T ⟶ S) (d : ℕ), IsFinite f ∧ Etale f ∧
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d ∧ ¬ ℓ ∣ d ∧
      ∃ X : RelSeries (ConstantRankOneStep.{0} ℓ ((smallEtalePullbackZMod.{0} ℓ f).obj F)),
        IsZero (Subobject.underlying.obj X.head) ∧ IsIso X.last.arrow := by
  classical
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨p⟩ : Nonempty S := inferInstance
  obtain ⟨s⟩ : Nonempty (GeometricPoint S) := ⟨S.algClosedPoint p⟩
  let B := BigEtaleSite.containing S
  let XS : B.Scheme := ⟨S, BigEtaleSite.contains_containing S⟩
  have : ConnectedSpace XS.1 := inferInstanceAs (ConnectedSpace S)
  let Xc : FiniteEtaleOver S := (representingCover B XS).obj (zmodFibreSetSheaf ℓ B XS ⟨F, hF⟩)
  -- the monodromy group on the fibre of the representing cover, and an `ℓ`-Sylow subgroup
  let ρ : EtaleFundamentalGroup S s →* Equiv.Perm ((finiteEtaleFiberFunctor s).obj Xc) :=
    MulAction.toPermHom _ _
  let Gρ := ρ.range
  let H : Sylow ℓ Gρ := Classical.arbitrary _
  let rb := ρ.rangeRestrict
  -- its preimage is an open subgroup
  have hle : ρ.ker ≤ (H : Subgroup Gρ).comap rb := fun τ hτ ↦ by
    have : rb τ = 1 := Subtype.ext hτ
    simp [Subgroup.mem_comap, this]
  let U : OpenSubgroup (EtaleFundamentalGroup S s) :=
    ⟨(H : Subgroup Gρ).comap rb,
      Subgroup.isOpen_mono hle (isOpen_ker_toPermHom_finiteEtaleFiber s Xc)⟩
  refine exists_primeToEll_finiteEtale_relSeries_of_openSubgroup hℓ XS F hF s U ?_ ?_
  -- the degree is the index of the Sylow subgroup, which is prime to `ℓ`
  · show ¬ ℓ ∣ ((H : Subgroup Gρ).comap rb).index
    rw [Subgroup.index_comap_of_surjective _ ρ.rangeRestrict_surjective]
    exact H.not_dvd_index
  -- the stabiliser condition
  · intro _ τ hτ
    obtain ⟨k, hk⟩ := H.isPGroup' ⟨rb τ, hτ⟩
    refine ⟨k, fun q ↦ ?_⟩
    have h1 : rb (τ ^ (ℓ ^ k)) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    exact congrArg (fun g : Equiv.Perm _ ↦ g q) (congrArg Subtype.val h1)

end Stacks.EtaleCohomology

end
