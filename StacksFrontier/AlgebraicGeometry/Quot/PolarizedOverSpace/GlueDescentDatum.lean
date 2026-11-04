module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedOverSpace.GluePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.ReadAlong
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.EtaleCoveringEffective
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FpqcDescentTransitivity

/-!
# The polarization of Stacks 0E94, descended to the glued algebraic space

Let `G` be a functor over the site from the points of `T` to the polarized families of
`AlgebraicGeometry.PolarizedOverSpace.RepresentedPolarized` (the right-hand side of Stacks 0E94),
and let `X` be the algebraic space glued from its families of schemes (Stacks 0E93), with the maps
`s_a : Z_a ⟶ X` from the families `Z_a` of `G` at the points `a` of `T`. For a morphism of points
`u : a' ⟶ a`, `G` gives an isomorphism `κ_u : M_{a'} ≅ g_u^* M_a` of the modules of `G` along the
map `g_u : Z_{a'} ⟶ Z_a`, and these compose
(`AlgebraicGeometry.PolarizedOverSpace.fiberIso_comp_law`).

Following the hint of Stacks 0E94, the module `M₀` of `G` at an atlas `U₀ ⟶ T` is descended along
the étale covering `s₀ : Z₀ ⟶ X` (Stacks 041F) by Stacks 04W8: the pairwise isomorphism on
`Z₀ ×_X Z₀` is `κ_{u₁}⁻¹ ≫ κ_{u₂}` read on the family at the product point `U₀ ×_T U₀`, which is
`Z₀ ×_X Z₀` (`AlgebraicGeometry.PolarizedOverSpace.isPullback_famMap_prodPoint`), and the cocycle
condition holds on the family at `U₀ ×_T U₀ ×_T U₀`, through which every triple of compatible
morphisms factors, because there all three pairwise isomorphisms are of the form `μᵢ⁻¹ ≫ μⱼ`.

## Main definitions

* `AlgebraicGeometry.PolarizedOverSpace.fiberIso`: the isomorphism of modules of a morphism of
  `RepresentedPolarized`.
* `AlgebraicGeometry.PolarizedOverSpace.glueDescentDatum`: the descent datum on `Z₀ ⟶ X`.
* `AlgebraicGeometry.PolarizedOverSpace.glueModule`: the descended module `L` on `X`, with
  `AlgebraicGeometry.PolarizedOverSpace.glueModuleIso : M₀ ≅ s₀^* L`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Pseudofunctor.CoGrothendieck

universe u

namespace AlgebraicGeometry.PolarizedOverSpace

attribute [local implicit_reducible] Stack.fibredCategory BasedCategory.ofFunctor schemeSpace
  Functor.toPseudofunctor' pseudofunctorOfIsLocallyDiscrete typeToGrpd Grpd.forgetToCat
  MorphismProperty

-- Elaboration compares the inverse images of the pseudofunctor with the functors themselves
-- without unfolding the latter.
attribute [local irreducible] Space.modulePullback Space.modulePullbackCompIso

-- The morphisms of the Grothendieck construction carry the quiver of `CategoryStruct`.
attribute [-instance] CategoryTheory.catToReflQuiver

variable {B : BigFppfSite.{u}}

section Fiber

variable {X Y Z : RepresentedPolarized B}

/-- **The isomorphism of modules of a morphism of `RepresentedPolarized`**, `M ≅ g^* M'` along
the map `g` of total spaces. -/
def fiberIso (f : X ⟶ Y) :
    (X.obj.obj.fiber : Space.Modules.{u, u} B integerBase (hZ B)
        (yoneda.obj X.obj.obj.base.left) (isAlgebraicSpace_yoneda B integerBase (hZ B) _)) ≅
      (Space.modulePullback B integerBase (hZ B)
        (Space.representedSpaceMap B integerBase (hZ B) f.hom.hom.base.left)).obj
        Y.obj.obj.fiber :=
  @asIso _ _ _ _ f.hom.hom.fiber (isIso_fiber f)

/-- The forward map of `fiberIso f` is the morphism of modules underlying `f`. -/
theorem fiberIso_hom (f : X ⟶ Y) : (fiberIso f).hom = f.hom.hom.fiber := rfl

/-- The inverse of the comparison of an iterated inverse image along represented morphisms is
the comparison `AlgebraicGeometry.Space.representedModulePullbackCompIso`. -/
theorem pullbackComparison_representedSpaceMap_inv {U V W : Site B} (h : U ⟶ V) (g : V ⟶ W)
    (k : U ⟶ W) (hk : h ≫ g = k)
    (hb : Space.representedSpaceMap B integerBase (hZ B) h ≫
      Space.representedSpaceMap B integerBase (hZ B) g =
      Space.representedSpaceMap B integerBase (hZ B) k)
    (N : Space.Modules.{u, u} B integerBase (hZ B) (yoneda.obj W)
      (isAlgebraicSpace_yoneda B integerBase (hZ B) _)) :
    (Space.QuasiCoherentDescent.pullbackComparison B integerBase (hZ B) _ _ _ hb N).inv =
      (Space.representedModulePullbackCompIso B integerBase (hZ B) h g).hom.app N ≫
        eqToHom (congrArg (fun q => (Space.modulePullback B integerBase (hZ B)
          (Space.representedSpaceMap B integerBase (hZ B) q)).obj N) hk) := by
  subst hk
  refine (Space.QuasiCoherentDescent.pullbackComparison_inv _ _ _ hb N).trans ?_
  refine Eq.symm ((congrArg (· ≫ _) ((NatTrans.comp_app _ _ N).trans
    (congrArg (_ ≫ ·) (eqToHom_app (congrArg (Space.modulePullback B integerBase (hZ B))
      (Space.representedSpaceMap_comp B integerBase (hZ B) h g)) N)))).trans ?_)
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (eqToHom_trans _ _))

/-- **The isomorphisms of modules of a composite compose**, through the comparison of iterated
inverse images of Stacks 03LU. -/
theorem fiberIso_comp_law (f : X ⟶ Y) (g : Y ⟶ Z) (m : X ⟶ Z) (hm : f ≫ g = m)
    (hb : Space.representedSpaceMap B integerBase (hZ B) f.hom.hom.base.left ≫
      Space.representedSpaceMap B integerBase (hZ B) g.hom.hom.base.left =
      Space.representedSpaceMap B integerBase (hZ B) m.hom.hom.base.left) :
    fiberIso f ≪≫ (Space.modulePullback B integerBase (hZ B)
        (Space.representedSpaceMap B integerBase (hZ B) f.hom.hom.base.left)).mapIso
        (fiberIso g) ≪≫
      (Space.QuasiCoherentDescent.pullbackComparison B integerBase (hZ B) _ _ _ hb
        Z.obj.obj.fiber).symm = fiberIso m := by
  subst hm
  apply Iso.ext
  have e₁ := fiber_comp f g
  have e₂ := arrowModules_map_map B f.hom.hom.base g.hom.hom.fiber
  have e₃ := arrowModules_mapComp_inv_app B f.hom.hom.base g.hom.hom.base Z.obj.obj.fiber
  have e₅ : (Space.QuasiCoherentDescent.pullbackComparison B integerBase (hZ B) _ _ _ hb
      Z.obj.obj.fiber).inv = (Space.representedModulePullbackCompIso B integerBase (hZ B)
        f.hom.hom.base.left g.hom.hom.base.left).hom.app Z.obj.obj.fiber :=
    (pullbackComparison_representedSpaceMap_inv f.hom.hom.base.left g.hom.hom.base.left
      _ rfl hb Z.obj.obj.fiber).trans
      ((congrArg (_ ≫ ·) (eqToHom_refl _ _)).trans (Category.comp_id _))
  refine ((Iso.trans_hom _ _).trans (congrArg (_ ≫ ·) ((Iso.trans_hom _ _).trans
    (congrArg₂ (· ≫ ·) (Functor.mapIso_hom _ _) ((Iso.symm_hom _).trans e₅))))).trans ?_
  exact (e₁.trans (congrArg (f.hom.hom.fiber ≫ ·) ((congrArg (· ≫ _) e₂).trans
    (congrArg (_ ≫ ·) e₃)))).symm

end Fiber

variable {T : AlgebraicSpaces B integerBase (hZ B)}
  (G : Points T ⥤ᵇ BasedCategory.ofFunctor (representedPolarizedProjection B))

/-- The families of algebraic spaces underlying `G`. -/
abbrev glueFamilies := BasedFunctor.comp G (forgetModulesBased B)

/-- **The algebraic space glued from the families of `G`** (Stacks 0E93). -/
abbrev glueTotal : AlgebraicSpaces B integerBase (hZ B) :=
  SpacesOverSpace.glueSpace (glueFamilies G)

/-- The total space of the family of `G` at a point. -/
abbrev chart (a : (Points T).obj) : AlgebraicSpaces B integerBase (hZ B) :=
  ⟨yoneda.obj (G.obj a).obj.obj.base.left, isAlgebraicSpace_yoneda B integerBase (hZ B) _⟩

/-- The map from the family of `G` at a point to the glued space. -/
abbrev chartMap (a : (Points T).obj) : chart G a ⟶ glueTotal G :=
  ObjectProperty.homMk (SpacesOverSpace.famToGlue (glueFamilies G) a)

/-- The map of total spaces of the cartesian square of `G` at a morphism of points. -/
abbrev chartHom {a' a : (Points T).obj} (u : a' ⟶ a) : chart G a' ⟶ chart G a :=
  Space.representedSpaceMap B integerBase (hZ B) (G.map u).hom.hom.base.left

/-- The module of `G` at a point. -/
abbrev chartModule (a : (Points T).obj) :
    Space.Modules.{u, u} B integerBase (hZ B) (chart G a).1 (chart G a).2 :=
  (G.obj a).obj.obj.fiber

/-- The map of charts along a morphism of points commutes with the maps to the glued space. -/
theorem chartHom_comp_chartMap {a' a : (Points T).obj} (u : a' ⟶ a) :
    chartHom G u ≫ chartMap G a = chartMap G a' :=
  ObjectProperty.hom_ext _ (SpacesOverSpace.famMap_comp_famToGlue (glueFamilies G) u)

/-- The maps of charts along composable morphisms of points compose. -/
theorem chartHom_comp {a'' a' a : (Points T).obj} (v : a'' ⟶ a') (u : a' ⟶ a) (m : a'' ⟶ a)
    (hm : v ≫ u = m) : chartHom G v ≫ chartHom G u = chartHom G m := by
  subst hm
  refine (Space.representedSpaceMap_comp B integerBase (hZ B) _ _).trans ?_
  simp only [chartHom, G.map_comp]
  rfl

/-- The composition law of the isomorphisms of modules of `G`. -/
theorem fiberIso_map_comp_law {a'' a' a : (Points T).obj} (v : a'' ⟶ a') (u : a' ⟶ a)
    (m : a'' ⟶ a) (hm : v ≫ u = m) :
    fiberIso (G.map v) ≪≫ (Space.modulePullback B integerBase (hZ B) (chartHom G v)).mapIso
        (fiberIso (G.map u)) ≪≫
      (Space.QuasiCoherentDescent.pullbackComparison B integerBase (hZ B) _ _ _
        (chartHom_comp G v u m hm) (chartModule G a)).symm = fiberIso (G.map m) :=
  fiberIso_comp_law (G.map v) (G.map u) (G.map m) (by rw [← hm, G.map_comp]) _

/-- **The family of `G` at the product point `a ×_T b` is the fibre product of the families at
`a` and `b` over the glued space.** -/
theorem isPullback_chart (a b : (Points T).obj) :
    IsPullback (chartHom G (prodPointFst a b)) (chartHom G (prodPointSnd a b)) (chartMap G a)
      (chartMap G b) :=
  IsPullback.of_map (ObjectProperty.ι _)
    (ObjectProperty.hom_ext _ (isPullback_famMap_prodPoint (glueFamilies G) a b).w)
    (isPullback_famMap_prodPoint (glueFamilies G) a b)

section Descent

/-- The atlas of `T`, as a point. -/
abbrev atlas₀ : (Points T).obj := atlasPoint T

/-- The product point `U₀ ×_T U₀`. -/
abbrev atlas₁ : (Points T).obj := prodPoint (atlasPoint T) (atlasPoint T)

/-- The product point `U₀ ×_T U₀ ×_T U₀`. -/
abbrev atlas₂ : (Points T).obj := prodPoint (atlas₁ (T := T)) (atlasPoint T)

/-- The pairwise isomorphism on the family at `U₀ ×_T U₀`. -/
abbrev glueTheta :
    (Space.modulePullback B integerBase (hZ B)
        (chartHom G (prodPointFst (atlasPoint T) (atlasPoint T)))).obj
        (chartModule G (atlasPoint T)) ≅
      (Space.modulePullback B integerBase (hZ B)
        (chartHom G (prodPointSnd (atlasPoint T) (atlasPoint T)))).obj
        (chartModule G (atlasPoint T)) :=
  (fiberIso (G.map (prodPointFst (atlasPoint T) (atlasPoint T)))).symm ≪≫
    fiberIso (G.map (prodPointSnd (atlasPoint T) (atlasPoint T)))

/-- The fibre product `Z₀ ×_X Z₀`, mapped to the family at `U₀ ×_T U₀`. -/
def gluePairMap :
    Space.QuasiCoherentDescent.pair B integerBase (hZ B) (fun _ : Unit => chart G (atlasPoint T))
        (fun _ => chartMap G (atlasPoint T)) () () ⟶ chart G atlas₁ :=
  ObjectProperty.homMk (isPullback_famMap_prodPoint (glueFamilies G) (atlasPoint T)
    (atlasPoint T)).isoPullback.inv

/-- `gluePairMap` followed by the first projection is the first projection of `Z₀ ×_X Z₀`. -/
theorem gluePairMap_fst :
    gluePairMap G ≫ chartHom G (prodPointFst (atlasPoint T) (atlasPoint T)) =
      Space.QuasiCoherentDescent.pairFst B integerBase (hZ B)
        (fun _ : Unit => chart G (atlasPoint T)) (fun _ => chartMap G (atlasPoint T)) () () :=
  ObjectProperty.hom_ext _ (IsPullback.isoPullback_inv_fst _)

/-- `gluePairMap` followed by the second projection is the second projection of `Z₀ ×_X Z₀`. -/
theorem gluePairMap_snd :
    gluePairMap G ≫ chartHom G (prodPointSnd (atlasPoint T) (atlasPoint T)) =
      Space.QuasiCoherentDescent.pairSnd B integerBase (hZ B)
        (fun _ : Unit => chart G (atlasPoint T)) (fun _ => chartMap G (atlasPoint T)) () () :=
  ObjectProperty.hom_ext _ (IsPullback.isoPullback_inv_snd _)

/-- The first projection `U₀ ×_T U₀ ×_T U₀ ⟶ U₀ ×_T U₀`. -/
abbrev triple₁₂ : (atlas₂ (T := T)) ⟶ atlas₁ := prodPointFst atlas₁ (atlasPoint T)

/-- The projection `U₀ ×_T U₀ ×_T U₀ ⟶ U₀` to the third factor. -/
abbrev tripleπ₃ : (atlas₂ (T := T)) ⟶ atlasPoint T := prodPointSnd atlas₁ (atlasPoint T)

/-- The projection to the first factor. -/
abbrev tripleπ₁ : (atlas₂ (T := T)) ⟶ atlasPoint T :=
  triple₁₂ ≫ prodPointFst (atlasPoint T) (atlasPoint T)

/-- The projection to the second factor. -/
abbrev tripleπ₂ : (atlas₂ (T := T)) ⟶ atlasPoint T :=
  triple₁₂ ≫ prodPointSnd (atlasPoint T) (atlasPoint T)

/-- The projection to the second and third factors. -/
abbrev triple₂₃ : (atlas₂ (T := T)) ⟶ atlas₁ := prodPointLift tripleπ₂ tripleπ₃

/-- The projection to the first and third factors. -/
abbrev triple₁₃ : (atlas₂ (T := T)) ⟶ atlas₁ := prodPointLift tripleπ₁ tripleπ₃

/-- The pairwise isomorphism of `G` read along a map into `U₀ ×_T U₀` is `μₚ⁻¹ ≫ μ_q`. -/
private theorem readAlong_glueTheta_eq {c : (Points T).obj} (k : c ⟶ atlas₁)
    (p q : c ⟶ atlasPoint T) (hp : k ≫ prodPointFst _ _ = p) (hq : k ≫ prodPointSnd _ _ = q) :
    Space.QuasiCoherentDescent.readAlong _ _ (glueTheta G) (chartHom G k) (chartHom G p)
      (chartHom G q) (chartHom_comp G _ _ _ hp) (chartHom_comp G _ _ _ hq) =
      (fiberIso (G.map p)).symm ≪≫ fiberIso (G.map q) :=
  Space.QuasiCoherentDescent.readAlong_eq_of_comp_law _ _ _ _ _ _ _ _ _ _ _ _
    (fiberIso_map_comp_law G k _ p hp) (fiberIso_map_comp_law G k _ q hq)

/-- **The cocycle condition on the family at `U₀ ×_T U₀ ×_T U₀`**: there the three pairwise
isomorphisms read `μᵢ⁻¹ ≫ μⱼ`, with `μᵢ` the isomorphism of modules of `G` along the `i`-th
projection. -/
theorem glueTheta_cocycle_triple :
    Space.QuasiCoherentDescent.readAlong _ _ (glueTheta G) (chartHom G triple₁₂)
        (chartHom G tripleπ₁) (chartHom G tripleπ₂) (chartHom_comp G _ _ _ rfl)
        (chartHom_comp G _ _ _ rfl) ≪≫
      Space.QuasiCoherentDescent.readAlong _ _ (glueTheta G) (chartHom G triple₂₃)
        (chartHom G tripleπ₂) (chartHom G tripleπ₃) (chartHom_comp G _ _ _ (prodPointLift_fst _ _))
        (chartHom_comp G _ _ _ (prodPointLift_snd _ _)) =
      Space.QuasiCoherentDescent.readAlong _ _ (glueTheta G) (chartHom G triple₁₃)
        (chartHom G tripleπ₁) (chartHom G tripleπ₃) (chartHom_comp G _ _ _ (prodPointLift_fst _ _))
        (chartHom_comp G _ _ _ (prodPointLift_snd _ _)) := by
  have A₁₂ := readAlong_glueTheta_eq G triple₁₂ tripleπ₁ tripleπ₂ rfl rfl
  have A₂₃ := readAlong_glueTheta_eq G triple₂₃ tripleπ₂ tripleπ₃ (prodPointLift_fst _ _)
    (prodPointLift_snd _ _)
  have A₁₃ := readAlong_glueTheta_eq G triple₁₃ tripleπ₁ tripleπ₃ (prodPointLift_fst _ _)
    (prodPointLift_snd _ _)
  exact (congrArg₂ (· ≪≫ ·) A₁₂ A₂₃).trans (((Iso.trans_assoc _ _ _).trans
    (congrArg (_ ≪≫ ·) (Iso.self_symm_id_assoc _ _))).trans A₁₃.symm)

/-- **The cocycle condition on every algebraic space**: three compatible morphisms into the
family at `U₀ ×_T U₀` factor through the family at `U₀ ×_T U₀ ×_T U₀`, which is
`Z₀ ×_X Z₀ ×_X Z₀`. -/
theorem glueTheta_cocycle (T' : AlgebraicSpaces B integerBase (hZ B))
    (w₁₂ w₂₃ w₁₃ : T' ⟶ chart G atlas₁) (v₁ v₂ v₃ : T' ⟶ chart G (atlasPoint T))
    (e₁₂ : w₁₂ ≫ chartHom G (prodPointFst (atlasPoint T) (atlasPoint T)) = v₁)
    (e₁₂' : w₁₂ ≫ chartHom G (prodPointSnd (atlasPoint T) (atlasPoint T)) = v₂)
    (e₂₃ : w₂₃ ≫ chartHom G (prodPointFst (atlasPoint T) (atlasPoint T)) = v₂)
    (e₂₃' : w₂₃ ≫ chartHom G (prodPointSnd (atlasPoint T) (atlasPoint T)) = v₃)
    (e₁₃ : w₁₃ ≫ chartHom G (prodPointFst (atlasPoint T) (atlasPoint T)) = v₁)
    (e₁₃' : w₁₃ ≫ chartHom G (prodPointSnd (atlasPoint T) (atlasPoint T)) = v₃) :
    Space.QuasiCoherentDescent.readAlong _ _ (glueTheta G) w₁₂ v₁ v₂ e₁₂ e₁₂' ≪≫
        Space.QuasiCoherentDescent.readAlong _ _ (glueTheta G) w₂₃ v₂ v₃ e₂₃ e₂₃' =
      Space.QuasiCoherentDescent.readAlong _ _ (glueTheta G) w₁₃ v₁ v₃ e₁₃ e₁₃' := by
  have sq₂ := isPullback_chart G atlas₁ (atlasPoint T)
  have sq₁ := isPullback_chart G (atlasPoint T) (atlasPoint T)
  have hc₁ := chartHom_comp_chartMap G (prodPointFst (atlasPoint T) (atlasPoint T))
  have hw : w₁₂ ≫ chartMap G atlas₁ = v₃ ≫ chartMap G (atlasPoint T) := by
    rw [← hc₁, ← Category.assoc, e₁₂, ← e₁₃, Category.assoc, hc₁,
      ← chartHom_comp_chartMap G (prodPointSnd (atlasPoint T) (atlasPoint T)), ← Category.assoc,
      e₁₃']
  have ht₁₂ : sq₂.lift w₁₂ v₃ hw ≫ chartHom G triple₁₂ = w₁₂ := sq₂.lift_fst _ _ _
  have htπ₃ : sq₂.lift w₁₂ v₃ hw ≫ chartHom G tripleπ₃ = v₃ := sq₂.lift_snd _ _ _
  have htπ₁ : sq₂.lift w₁₂ v₃ hw ≫ chartHom G tripleπ₁ = v₁ := by
    rw [← chartHom_comp G triple₁₂ (prodPointFst _ _) tripleπ₁ rfl, ← Category.assoc, ht₁₂, e₁₂]
  have htπ₂ : sq₂.lift w₁₂ v₃ hw ≫ chartHom G tripleπ₂ = v₂ := by
    rw [← chartHom_comp G triple₁₂ (prodPointSnd _ _) tripleπ₂ rfl, ← Category.assoc, ht₁₂, e₁₂']
  have ht₂₃ : sq₂.lift w₁₂ v₃ hw ≫ chartHom G triple₂₃ = w₂₃ := by
    refine sq₁.hom_ext ?_ ?_
    · rw [Category.assoc, chartHom_comp G triple₂₃ (prodPointFst _ _) tripleπ₂
        (prodPointLift_fst _ _), htπ₂, e₂₃]
    · rw [Category.assoc, chartHom_comp G triple₂₃ (prodPointSnd _ _) tripleπ₃
        (prodPointLift_snd _ _), htπ₃, e₂₃']
  have ht₁₃ : sq₂.lift w₁₂ v₃ hw ≫ chartHom G triple₁₃ = w₁₃ := by
    refine sq₁.hom_ext ?_ ?_
    · rw [Category.assoc, chartHom_comp G triple₁₃ (prodPointFst _ _) tripleπ₁
        (prodPointLift_fst _ _), htπ₁, e₁₃]
    · rw [Category.assoc, chartHom_comp G triple₁₃ (prodPointSnd _ _) tripleπ₃
        (prodPointLift_snd _ _), htπ₃, e₁₃']
  exact Space.QuasiCoherentDescent.readAlong_cocycle_of_triple _ _ (glueTheta G)
    (chartHom G triple₁₂) (chartHom G triple₂₃) (chartHom G triple₁₃) (chartHom G tripleπ₁)
    (chartHom G tripleπ₂) (chartHom G tripleπ₃) (chartHom_comp G _ _ _ rfl)
    (chartHom_comp G _ _ _ rfl) (chartHom_comp G _ _ _ (prodPointLift_fst _ _))
    (chartHom_comp G _ _ _ (prodPointLift_snd _ _)) (chartHom_comp G _ _ _ (prodPointLift_fst _ _))
    (chartHom_comp G _ _ _ (prodPointLift_snd _ _)) (glueTheta_cocycle_triple G)
    (sq₂.lift w₁₂ v₃ hw) w₁₂ w₂₃ w₁₃ v₁ v₂ v₃ ht₁₂ ht₂₃ ht₁₃ htπ₁ htπ₂ htπ₃ e₁₂ e₁₂' e₂₃ e₂₃'
    e₁₃ e₁₃'

/-- **The descent datum on the base change `Z₀ ⟶ X` of the atlas** (Stacks 04W3): the module of
`G` at the atlas, with the pairwise isomorphism read from `G` on `U₀ ×_T U₀`. -/
def glueDescentDatum :
    Space.QuasiCoherentDescent.DescentDatum B integerBase (hZ B)
      (fun _ : Unit => chart G (atlasPoint T)) (fun _ => chartMap G (atlasPoint T)) :=
  Space.QuasiCoherentDescent.unitDescentDatum _ _ (glueTheta G) (chartMap G (atlasPoint T))
    (G.obj (atlasPoint T)).obj.property.quasicoherent (gluePairMap G) (gluePairMap_fst G)
    (gluePairMap_snd G) (glueTheta_cocycle G)

/-- **The descent datum is effective** (Stacks 04W8): `Z₀ ⟶ X` is an étale covering. -/
theorem isEffective_glueDescentDatum :
    Space.QuasiCoherentDescent.IsEffective B integerBase (hZ B) _ _ (glueDescentDatum G) :=
  Space.QuasiCoherentDescent.isEffective_of_isEtaleCovering B integerBase (hZ B) _ _
    (fun _ => (isEtaleCovering_famToGlue_atlasPoint (glueFamilies G)).etale ())
    (isEtaleCovering_famToGlue_atlasPoint (glueFamilies G)) _

/-- **The descended module `L` on the glued space.** -/
def glueModule : Space.Modules.{u, u} B integerBase (hZ B) (glueTotal G).1 (glueTotal G).2 :=
  (isEffective_glueDescentDatum G).choose

/-- The descended module `L` on the glued space is quasi-coherent. -/
theorem isQuasicoherentOnSite_glueModule : (glueModule G).IsQuasicoherentOnSite :=
  (isEffective_glueDescentDatum G).choose_spec.choose

/-- The isomorphism of the descent datum with the canonical descent datum of `L`. -/
def glueDatumIso : glueDescentDatum G ≅ Space.QuasiCoherentDescent.canonicalDescentDatum B
    integerBase (hZ B) _ _ (glueModule G) (isQuasicoherentOnSite_glueModule G) :=
  (isEffective_glueDescentDatum G).choose_spec.choose_spec.some

/-- **The module of `G` at the atlas is the inverse image of `L`**, `M₀ ≅ s₀^* L`. -/
def glueModuleIso : chartModule G (atlasPoint T) ≅
    (Space.modulePullback B integerBase (hZ B) (chartMap G (atlasPoint T))).obj (glueModule G) :=
  Space.QuasiCoherentDescent.DescentDatum.appIso B integerBase (hZ B) (glueDatumIso G) ()

end Descent

end AlgebraicGeometry.PolarizedOverSpace

end
