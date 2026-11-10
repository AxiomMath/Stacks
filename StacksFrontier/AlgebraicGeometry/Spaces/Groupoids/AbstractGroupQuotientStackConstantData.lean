module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.AbstractGroupQuotientStackComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.ConstantGroup
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.TrivialTorsorWithMap
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ConstantSheaf

/-!
# The constant group algebraic space `G_S`, its action on `X`, and the constant group data

Let `S` be a scheme of a big fppf site, `G` an abstract group whose constant group scheme `G_S`
lies in the site, `X` a sheaf on `(Sch/S)_fppf` and `ρ : G →* Aut X` an action. The last clause
of Stacks 0371 compares `[[X/G]]` with the quotient `[[X/G_S]]` of Situation 04WL, for which `X`
is an algebraic space over `S` acted on by the group algebraic space `G_S`. This file supplies
the two pieces of data the comparison functor
`AlgebraicGeometry.Space.torsorWithMapToAbstractQuotient` consumes.

## Main definitions

* `AlgebraicGeometry.Space.actGlue`: a point of `G_S` over `V` is a locally constant map
  `V → G` (Stacks 03YW); it acts on a section of `X` over `V` by gluing the actions of its
  values, using that `X` is a sheaf.
* `AlgebraicGeometry.Space.constGSModObj`: the resulting action of `G_S` on `X` over `S`.
* `AlgebraicGeometry.Space.constGSData`: the identification of `G_U = U ×_S G_S` with the
  constant sheaf of groups on `(Sch/U)_fppf`, compatible with base change, from the
  representation of the constant sheaf by `G_S` (Stacks 03P5, the middle clause of 0371).

## Main results

* `AlgebraicGeometry.Space.constGS_isCompatibleAction`: under that identification the constant
  section `g` of `G_S` acts on `X` as `ρ g` does.
* `AlgebraicGeometry.Space.constGS_eq`: the group algebraic space used here is
  `AlgebraicGeometry.Space.constantGroupSpace` at the base `S`, by definition.

## Implementation notes

The module object is built from an action on points (`CategoryTheory.ModObj.ofHomAction`), and
the action, the identification and their compatibility are first constructed for an arbitrary
group algebraic space of the form `ptsGS F r` (points given by a presheaf of groups `F`), then
specialised to `G_S`. Elaboration of terms mentioning the constant group scheme is expensive,
and the generic statements keep it out of the instance problems.

## References

* [Stacks Project, Tag 0371](https://stacks.math.columbia.edu/tag/0371)
* [Stacks Project, Tag 03YW](https://stacks.math.columbia.edu/tag/03YW)
* [Stacks Project, Tag 03P5](https://stacks.math.columbia.edu/tag/03P5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory MonObj

universe t v u

namespace CategoryTheory

open CartesianMonoidalCategory

universe w₁ w₂

variable {C : Type w₁} [Category.{w₂} C] [CartesianMonoidalCategory C] {M X : C} [MonObj M]

/-- A module object structure from an action on points: a family of actions of the monoids
`Z ⟶ M` on the sets `Z ⟶ X`, natural in `Z`. -/
@[reducible]
def ModObj.ofHomAction (a : ∀ Z : C, (Z ⟶ M) → (Z ⟶ X) → (Z ⟶ X))
    (comp : ∀ {Z Z' : C} (g : Z' ⟶ Z) (m : Z ⟶ M) (x : Z ⟶ X), g ≫ a Z m x = a Z' (g ≫ m) (g ≫ x))
    (one : ∀ (Z : C) (x : Z ⟶ X), a Z 1 x = x)
    (mul : ∀ (Z : C) (m n : Z ⟶ M) (x : Z ⟶ X), a Z (m * n) x = a Z m (a Z n x)) :
    ModObj M X where
  smul := a _ (fst M X) (snd M X)
  one_smul := by
    change η[M] ▷ X ≫ a _ (fst M X) (snd M X) = (λ_ X).hom
    rw [comp]
    have h1 : η[M] ▷ X ≫ fst M X = 1 := by
      rw [Hom.one_def, whiskerRight_fst]
      exact congrArg (· ≫ η[M]) (Subsingleton.elim _ _)
    rw [h1, whiskerRight_snd, one, leftUnitor_hom]
  mul_smul := by
    change μ[M] ▷ X ≫ a _ (fst M X) (snd M X) =
      (α_ M M X).hom ≫ M ◁ a _ (fst M X) (snd M X) ≫ a _ (fst M X) (snd M X)
    rw [comp, whiskerRight_snd]
    have h1 : μ[M] ▷ X ≫ fst M X = (fst _ X ≫ fst M M) * (fst _ X ≫ snd M M) := by
      rw [Hom.mul_def, whiskerRight_fst, ← comp_lift, lift_fst_snd, Category.comp_id]
    rw [h1, mul, comp, comp]
    congr 1
    · simp
    · rw [whiskerLeft_snd, ← Category.assoc, comp]
      congr 1 <;> simp

end CategoryTheory

namespace AlgebraicGeometry.Space

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}
  {G : Type (max (u + 1) v)} [Group G] [Small.{u} G]
  (hG : 𝒞.Contains (constantGroupScheme G S).X.left)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limits of presheaves on the big fppf site goes deep
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_absGrpQuotConstData :
    HasPullbacks ((BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_absGrpQuotConstData
    {X Y Z : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limits of presheaves on the big fppf site goes deep
/-- Discrete limits of presheaves on the big fppf site (instance search times out without
this shortcut). -/
local instance (priority := high) hasLimitsOfShapeDiscrete_presheaf_absGrpQuotConstData
    (J : Type) : HasLimitsOfShape (Discrete J) ((BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) :=
  inferInstance

/-! ### Points of the constant group scheme as locally constant maps -/

/-- The scheme underlying an object of the big fppf site of `S`. -/
abbrev sch (V : BigFppfOver 𝒞 S hS) : Scheme.{u} := ((toSchemeOver 𝒞 S hS).obj V).left

/-- The morphism of schemes underlying a morphism of the big fppf site of `S`. -/
abbrev schMap {V W : BigFppfOver 𝒞 S hS} (f : W ⟶ V) : sch W ⟶ sch V :=
  ((toSchemeOver 𝒞 S hS).map f).left

/-- The points of `G_S` over an object `V` of the site, read as the locally constant `G`-valued
maps on `V`, by Stacks 03YW. -/
def constPointsEquiv (V : BigFppfOver 𝒞 S hS) :
    (constantGroupPointsOnSite 𝒞 S hS G hG).obj (op V) ≃* LocallyConstant (sch V) G :=
  MulEquiv.ulift.symm.trans
    ((constantGroupSchemePointsIsoLocallyConstantMaps G S).app
      (op ((toSchemeOver 𝒞 S hS).obj V))).groupIsoToMulEquiv

/-- The restriction of a point of `G_S` along a morphism of the site. -/
abbrev ptsRes {V W : BigFppfOver 𝒞 S hS} (f : W ⟶ V)
    (gp : (constantGroupPointsOnSite 𝒞 S hS G hG).obj (op V)) :
    (constantGroupPointsOnSite 𝒞 S hS G hG).obj (op W) :=
  (constantGroupPointsOnSite 𝒞 S hS G hG ⋙ forget GrpCat).map f.op gp

/-- The locally constant map attached to a point of `G_S`, as a plain function. -/
def ptFun {V : BigFppfOver 𝒞 S hS}
    (gp : (constantGroupPointsOnSite 𝒞 S hS G hG).obj (op V)) : sch V → G :=
  constPointsEquiv hG V gp

/-- The locally constant map of the restriction of a point of `G_S` along `f` is the composite
of the locally constant map of the point with the morphism of schemes underlying `f`. -/
theorem ptFun_map {V W : BigFppfOver 𝒞 S hS} (f : W ⟶ V)
    (gp : (constantGroupPointsOnSite 𝒞 S hS G hG).obj (op V)) (w : sch W) :
    ptFun hG (ptsRes hG f gp) w = ptFun hG gp (schMap f w) := by
  have h := NatTrans.naturality_apply (constantGroupSchemePointsIsoLocallyConstantMaps G S).hom
    ((toSchemeOver 𝒞 S hS).map f).op
    (ULift.up gp : ((yonedaGrp.obj (constantGroupScheme G S) ⋙
      GrpCat.uliftFunctor.{max (u + 1) v}).obj (op ((toSchemeOver 𝒞 S hS).obj V))))
  exact congrArg (fun φ : LocallyConstant (sch W) G => φ w) h

/-- The map attached to a point of `G_S` is locally constant. -/
theorem isLocallyConstant_ptFun {V : BigFppfOver 𝒞 S hS}
    (gp : (constantGroupPointsOnSite 𝒞 S hS G hG).obj (op V)) :
    IsLocallyConstant (ptFun hG gp) :=
  (constPointsEquiv hG V gp).isLocallyConstant

/-- The unit point of `G_S` is the constant map with value `1`. -/
theorem ptFun_one {V : BigFppfOver 𝒞 S hS} (w : sch V) :
    ptFun hG (1 : (constantGroupPointsOnSite 𝒞 S hS G hG).obj (op V)) w = 1 := by
  rw [ptFun, map_one]
  rfl

/-- The map attached to a product of points of `G_S` is the pointwise product of their maps. -/
theorem ptFun_mul {V : BigFppfOver 𝒞 S hS}
    (a b : (constantGroupPointsOnSite 𝒞 S hS G hG).obj (op V)) (w : sch V) :
    ptFun hG (V := V) (a * b) w = ptFun hG a w * ptFun hG b w := by
  rw [ptFun, ptFun, ptFun, map_mul]
  rfl

/-- The morphism of schemes underlying a composite is the composite of the underlying
morphisms, on points. -/
theorem schMap_comp {U V W : BigFppfOver 𝒞 S hS} (h : U ⟶ W) (f : W ⟶ V) (z : sch U) :
    schMap (h ≫ f) z = schMap f (schMap h z) := by
  rw [schMap, Functor.map_comp, Over.comp_left, Scheme.Hom.comp_apply]

/-- The morphism of schemes underlying an identity is the identity on points. -/
theorem schMap_id {V : BigFppfOver 𝒞 S hS} (z : sch V) : schMap (𝟙 V) z = z := by
  rw [schMap, CategoryTheory.Functor.map_id]
  rfl

/-! ### The action of `G_S` on a sheaf with an action of `G` -/

/-- The sieve of the morphisms into `V` along which a function on the points of `V` is
constant. -/
def lcSieve {V : BigFppfOver 𝒞 S hS} {Y : Type*} (c : sch V → Y) : Sieve V where
  arrows W f := ∃ y : Y, ∀ w : sch W, c (schMap f w) = y
  downward_closed := by
    rintro W Z f ⟨y, hy⟩ h
    exact ⟨y, fun z => by rw [schMap_comp, hy]⟩

/-- A locally constant function on the points of `V` is constant along a covering sieve. -/
theorem lcSieve_mem {V : BigFppfOver 𝒞 S hS} {Y : Type*} {c : sch V → Y}
    (hc : IsLocallyConstant c) : lcSieve c ∈ BigFppfOver.topology 𝒞 S hS V := by
  let U : sch V → (sch V).Opens := fun y =>
    ⟨{z | c z = c y}, hc.isOpen_fiber _⟩
  have hU : TopologicalSpace.IsOpenCover U := by
    rw [TopologicalSpace.IsOpenCover]
    exact eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, rfl⟩
  obtain ⟨I, W, a, r, hcov, hmem⟩ := bigFppfOver_openCoverData 𝒞 S hS (T := V) U hU
  refine (BigFppfOver.topology 𝒞 S hS).superset_covering ?_ hcov
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  rintro _ _ ⟨i⟩
  exact ⟨c (r i), fun w => hmem i w⟩

/-- The sieve of the morphisms into `V` along which a point of `G_S` is constant. -/
abbrev constSieve {V : BigFppfOver 𝒞 S hS}
    (gp : (constantGroupPointsOnSite 𝒞 S hS G hG).obj (op V)) : Sieve V :=
  lcSieve (ptFun hG gp)

/-- A point of `G_S` is locally constant, so the sieve along which it is constant covers. -/
theorem constSieve_mem {V : BigFppfOver 𝒞 S hS}
    (gp : (constantGroupPointsOnSite 𝒞 S hS G hG).obj (op V)) :
    constSieve hG gp ∈ BigFppfOver.topology 𝒞 S hS V :=
  lcSieve_mem (isLocallyConstant_ptFun hG gp)

variable {X₀ : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u}
  (hX₀ : Presheaf.IsSheaf (BigFppfOver.topology 𝒞 S hS) X₀)

include hX₀ in
/-- A sheaf has at most one section over an object with empty underlying scheme. -/
theorem subsingleton_of_isEmpty {W : BigFppfOver 𝒞 S hS} (h : IsEmpty (sch W)) :
    Subsingleton (X₀.obj (op W)) := by
  have hbot : (⊥ : Sieve W) ∈ BigFppfOver.topology 𝒞 S hS W :=
    openCoverData_bottom (BigFppfOver.toScheme 𝒞 S hS) (BigFppfOver.topology 𝒞 S hS)
      (bigFppfOver_openCoverData 𝒞 S hS) h
  exact ⟨fun a b => ((isSheaf_iff_isSheaf_of_type _ _).1 hX₀ ⊥ hbot).isSeparatedFor.ext
    (fun _ _ hf => hf.elim)⟩

include hX₀ in
/-- Two sections of a sheaf agreeing along a covering sieve are equal. -/
theorem eq_of_mem_topology {V : BigFppfOver 𝒞 S hS} {R : Sieve V}
    (hR : R ∈ BigFppfOver.topology 𝒞 S hS V) {y y' : X₀.obj (op V)}
    (h : ∀ ⦃W : BigFppfOver 𝒞 S hS⦄ (f : W ⟶ V), R f → X₀.map f.op y = X₀.map f.op y') :
    y = y' :=
  ((isSheaf_iff_isSheaf_of_type _ _).1 hX₀ R hR).isSeparatedFor.ext h

variable (ρ₀ : G →* Aut X₀)

/-- The sections of the family glued into the action of a point of `G_S`. -/
def actFamily {V : BigFppfOver 𝒞 S hS}
    (gp : (constantGroupPointsOnSite 𝒞 S hS G hG).obj (op V)) (x : X₀.obj (op V)) :
    Presieve.FamilyOfElements X₀ (constSieve hG gp).arrows :=
  fun W f hf => (ρ₀ hf.choose).asIso.hom.app (op W) (X₀.map f.op x)

include hX₀ in
/-- The family `actFamily` of sections of a sheaf is compatible. -/
theorem actFamily_compatible {V : BigFppfOver 𝒞 S hS}
    (gp : (constantGroupPointsOnSite 𝒞 S hS G hG).obj (op V)) (x : X₀.obj (op V)) :
    (actFamily hG ρ₀ gp x).Compatible := by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hcomm
  simp only [actFamily]
  rw [NatTrans.naturality_apply, NatTrans.naturality_apply, ← Functor.map_comp_apply,
    ← Functor.map_comp_apply, ← op_comp, ← op_comp, hcomm]
  rcases isEmpty_or_nonempty (sch Z) with hZ | ⟨⟨z⟩⟩
  · exact (subsingleton_of_isEmpty hX₀ hZ).elim _ _
  · have e₁ := h₁.choose_spec (schMap g₁ z)
    have e₂ := h₂.choose_spec (schMap g₂ z)
    rw [← schMap_comp, hcomm, schMap_comp] at e₁
    rw [← schMap_comp, schMap_comp] at e₂
    rw [show h₁.choose = h₂.choose from e₁.symm.trans e₂]

/-- **The action of `G_S` on `X`.** A point `γ` of `G_S` over `V` is a locally constant map
`V → G`; it acts on a section `x` of `X` over `V` by the section which, over every morphism
`W ⟶ V` along which `γ` is constant with value `g`, is `ρ g` applied to the restriction of
`x`. -/
def actGlue {V : BigFppfOver 𝒞 S hS}
    (gp : (constantGroupPointsOnSite 𝒞 S hS G hG).obj (op V)) (x : X₀.obj (op V)) :
    X₀.obj (op V) :=
  ((isSheaf_iff_isSheaf_of_type _ _).1 hX₀ _ (constSieve_mem hG gp)).amalgamate
    (actFamily hG ρ₀ gp x) (actFamily_compatible hG hX₀ ρ₀ gp x)

/-- The action of a point of `G_S` restricted along a morphism along which the point is
constant with value `g` is the action of `g`. -/
theorem actGlue_spec {V W : BigFppfOver 𝒞 S hS}
    (gp : (constantGroupPointsOnSite 𝒞 S hS G hG).obj (op V)) (x : X₀.obj (op V))
    (f : W ⟶ V) (g : G) (hg : ∀ w : sch W, ptFun hG gp (schMap f w) = g) :
    X₀.map f.op (actGlue hG hX₀ ρ₀ gp x) = (ρ₀ g).asIso.hom.app (op W) (X₀.map f.op x) := by
  have hf : constSieve hG gp f := ⟨g, hg⟩
  rw [actGlue, Presieve.IsSheafFor.valid_glue _ _ _ hf]
  rcases isEmpty_or_nonempty (sch W) with hW | ⟨⟨w⟩⟩
  · exact (subsingleton_of_isEmpty hX₀ hW).elim _ _
  · have e : hf.choose = g := (hf.choose_spec w).symm.trans (hg w)
    simp only [actFamily, e]

/-- The action of points of `G_S` on `X` commutes with restriction along morphisms of the
site. -/
theorem actGlue_naturality {V W : BigFppfOver 𝒞 S hS} (h : W ⟶ V)
    (gp : (constantGroupPointsOnSite 𝒞 S hS G hG).obj (op V)) (x : X₀.obj (op V)) :
    X₀.map h.op (actGlue hG hX₀ ρ₀ gp x) =
      actGlue hG hX₀ ρ₀ (ptsRes hG h gp) (X₀.map h.op x) := by
  refine eq_of_mem_topology hX₀ (constSieve_mem hG (ptsRes hG h gp)) ?_
  rintro Z f ⟨g, hg⟩
  have hg' : ∀ z : sch Z, ptFun hG gp (schMap (f ≫ h) z) = g := fun z => by
    rw [schMap_comp, ← ptFun_map, hg]
  rw [actGlue_spec hG hX₀ ρ₀ _ _ f g hg, ← Functor.map_comp_apply, ← op_comp,
    actGlue_spec hG hX₀ ρ₀ gp x (f ≫ h) g hg', op_comp, Functor.map_comp_apply]

/-- The unit point of `G_S` acts trivially on `X`. -/
theorem actGlue_one {V : BigFppfOver 𝒞 S hS} (x : X₀.obj (op V)) :
    actGlue hG hX₀ ρ₀ (1 : (constantGroupPointsOnSite 𝒞 S hS G hG).obj (op V)) x = x := by
  refine eq_of_mem_topology hX₀ ((BigFppfOver.topology 𝒞 S hS).top_mem V) ?_
  intro W f _
  rw [actGlue_spec hG hX₀ ρ₀ _ _ f 1 (fun w => ptFun_one hG _), map_one]
  rfl

/-- A product `a * b` of points of `G_S` acts on `X` as `b` followed by `a`. -/
theorem actGlue_mul {V : BigFppfOver 𝒞 S hS}
    (a b : (constantGroupPointsOnSite 𝒞 S hS G hG).obj (op V)) (x : X₀.obj (op V)) :
    actGlue hG hX₀ ρ₀ (a * b) x = actGlue hG hX₀ ρ₀ a (actGlue hG hX₀ ρ₀ b x) := by
  refine eq_of_mem_topology hX₀ ((BigFppfOver.topology 𝒞 S hS).intersection_covering
    (constSieve_mem hG a) (constSieve_mem hG b)) ?_
  rintro W f ⟨⟨ga, ha⟩, ⟨gb, hb⟩⟩
  rw [actGlue_spec hG hX₀ ρ₀ _ _ f (ga * gb) (fun w => by rw [ptFun_mul, ha, hb]),
    actGlue_spec hG hX₀ ρ₀ _ _ f ga ha, actGlue_spec hG hX₀ ρ₀ _ _ f gb hb, map_mul]
  rfl

/-- A point of `G_S` over `V` that is constant with value `g` acts on `X` over `V` as
`ρ g`. -/
theorem actGlue_of_const {V : BigFppfOver 𝒞 S hS}
    (gp : (constantGroupPointsOnSite 𝒞 S hS G hG).obj (op V)) (x : X₀.obj (op V)) (g : G)
    (hg : ∀ w : sch V, ptFun hG gp w = g) :
    actGlue hG hX₀ ρ₀ gp x = (ρ₀ g).asIso.hom.app (op V) x := by
  simpa only [op_id, Functor.map_id_apply] using
    actGlue_spec hG hX₀ ρ₀ gp x (𝟙 V) g (fun w => by rw [schMap_id, hg])

/-! ### `S` as an algebraic space over itself, and `X` over it -/

variable (𝒞 S hS) in
/-- The terminal object `S` of the big fppf site of `S`. -/
abbrev finalObj : BigFppfOver 𝒞 S hS := Over.mk (𝟙 (𝒞.obj hS))

variable (𝒞 S hS) in
/-- `S` as a presheaf on its own big fppf site: the terminal presheaf. -/
abbrev baseS : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u := yoneda.obj (finalObj 𝒞 S hS)

variable (𝒞 S hS) in
/-- `S` is an algebraic space over itself. -/
theorem isAlgebraicSpace_baseS : IsAlgebraicSpace 𝒞 S hS (baseS 𝒞 S hS) :=
  isAlgebraicSpace_yoneda 𝒞 S hS _

/-- The structure morphism of a presheaf on the big fppf site of `S` to `S`. -/
def toBaseS (P : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) : P ⟶ baseS 𝒞 S hS where
  app T := ↾fun _ => Over.mkIdTerminal.from T.unop
  naturality _ _ _ := by ext; exact Over.mkIdTerminal.hom_ext _ _

/-- Any two morphisms into `S` agree. -/
theorem baseS_ext {P : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} (f g : P ⟶ baseS 𝒞 S hS) : f = g := by
  ext T x
  exact Over.mkIdTerminal.hom_ext _ _

/-- A presheaf on the big fppf site of `S`, as an object over `S`. -/
abbrev overBaseS (P : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) : Over (baseS 𝒞 S hS) :=
  Over.mk (toBaseS P)

/-! ### Actions of a group algebraic space given on points -/

section PointsAction

variable (F : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ GrpCat.{u}) {a₀ : BigFppfOver 𝒞 S hS}
  (r : (F ⋙ forget GrpCat).RepresentableBy a₀) (P : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
  (act : ∀ V : BigFppfOver 𝒞 S hS, F.obj (op V) → P.obj (op V) → P.obj (op V))
  (hnat : ∀ {V W : BigFppfOver 𝒞 S hS} (h : W ⟶ V) (g : F.obj (op V)) (x : P.obj (op V)),
    P.map h.op (act V g x) = act W (F.map h.op g) (P.map h.op x))

/-- The group algebraic space over `S` whose points are the sections of `F`. -/
abbrev ptsGS : GroupAlgebraicSpace 𝒞 S hS (baseS 𝒞 S hS) (isAlgebraicSpace_baseS 𝒞 S hS) :=
  GroupAlgebraicSpace.ofPointsFunctor 𝒞 S hS (baseS 𝒞 S hS) (isAlgebraicSpace_baseS 𝒞 S hS) F r

/-- The section of `F` underlying a point of `ptsGS F r`. -/
def ptSecF {Z : Over (baseS 𝒞 S hS)} (m : Z ⟶ (ptsGS F r).obj.X) (T : BigFppfOver 𝒞 S hS)
    (z : Z.left.obj (op T)) : F.obj (op T) :=
  (m.left ≫ prod.snd).app (op T) z

include hnat in
/-- The action on points of an object over `S`. -/
def actHomF (Z : Over (baseS 𝒞 S hS)) (m : Z ⟶ (ptsGS F r).obj.X) (x : Z ⟶ overBaseS P) :
    Z ⟶ overBaseS P :=
  Over.homMk
    { app T := ↾fun z => act T.unop (ptSecF F r m T.unop z) (x.left.app T z)
      naturality T T' h := by
        ext z
        change act T'.unop (ptSecF F r m T'.unop (Z.left.map h z))
          (x.left.app T' (Z.left.map h z)) = P.map h (act T.unop (ptSecF F r m T.unop z)
            (x.left.app T z))
        rw [NatTrans.naturality_apply, ptSecF, NatTrans.naturality_apply]
        exact (hnat h.unop _ _).symm }
    (baseS_ext _ _)

/-- On a point `z` of `Z` over `T`, the action on points is `act` applied to the sections of
`F` and of `P` at `z`. -/
theorem actHomF_left_app (Z : Over (baseS 𝒞 S hS)) (m : Z ⟶ (ptsGS F r).obj.X)
    (x : Z ⟶ overBaseS P) (T : BigFppfOver 𝒞 S hS) (z : Z.left.obj (op T)) :
    (actHomF F r P act hnat Z m x).left.app (op T) z =
      act T (ptSecF F r m T z) (x.left.app (op T) z) :=
  rfl

/-- The section of `F` underlying the unit point of `ptsGS F r` is `1`. -/
theorem ptSecF_one (Z : Over (baseS 𝒞 S hS)) (T : BigFppfOver 𝒞 S hS) (z : Z.left.obj (op T)) :
    ptSecF F r (1 : Z ⟶ (ptsGS F r).obj.X) T z = 1 := by
  change (overProdFstHomMulEquiv (baseS 𝒞 S hS) (F ⋙ forget GrpCat) Z 1).app (op T) z = 1
  rw [map_one]
  rfl

/-- The section of `F` underlying a product of points of `ptsGS F r` is the product of their
sections. -/
theorem ptSecF_mul (Z : Over (baseS 𝒞 S hS)) (m n : Z ⟶ (ptsGS F r).obj.X)
    (T : BigFppfOver 𝒞 S hS) (z : Z.left.obj (op T)) :
    ptSecF F r (m * n) T z = ptSecF F r m T z * ptSecF F r n T z := by
  have e := congrArg (fun φ : Z.left ⟶ F ⋙ forget GrpCat => φ.app (op T) z)
    (map_mul (overProdFstHomMulEquiv (baseS 𝒞 S hS) (F ⋙ forget GrpCat) Z) m n)
  refine e.trans ?_
  rw [Hom.mul_def, NatTrans.comp_app_apply, lift_app_apply]
  rfl

/-- **An action given on points**: a natural action of the sections of `F` on those of `P`
is an action of the group algebraic space `ptsGS F r` on `P` over `S`. -/
@[reducible]
def ptsModObj (hone : ∀ V (x : P.obj (op V)), act V 1 x = x)
    (hmul : ∀ V (g h : F.obj (op V)) (x : P.obj (op V)), act V (g * h) x = act V g (act V h x)) :
    ModObj (ptsGS F r).obj.X (overBaseS P) :=
  ModObj.ofHomAction (actHomF F r P act hnat)
    (fun g m x => Over.OverMorphism.ext (by ext T z; rfl))
    (fun Z x => Over.OverMorphism.ext (by
      ext ⟨T⟩ z
      exact (actHomF_left_app F r P act hnat Z 1 x T z).trans (by rw [ptSecF_one, hone]; rfl)))
    (fun Z m n x => Over.OverMorphism.ext (by
      ext ⟨T⟩ z
      refine (actHomF_left_app F r P act hnat Z _ _ T z).trans ?_
      rw [ptSecF_mul, hmul]
      rfl))

omit [Small.{u} G] in
/-- The sectionwise action of `ptsGS F r` on `P` is the given action. -/
theorem ptsModObj_smulSection (hone : ∀ V (x : P.obj (op V)), act V 1 x = x)
    (hmul : ∀ V (g h : F.obj (op V)) (x : P.obj (op V)), act V (g * h) x = act V g (act V h x))
    {V : BigFppfOver 𝒞 S hS} (gs : (ptsGS F r).obj.X.left.obj (op V)) (y : P.obj (op V))
    (h : (ptsGS F r).obj.X.hom.app (op V) gs = (overBaseS P).hom.app (op V) y) :
    letI := ptsModObj F r P act hnat hone hmul
    smulSection (ptsGS F r).obj.X (overBaseS P) gs y h =
      act V ((prod.snd : baseS 𝒞 S hS ⨯ (F ⋙ forget GrpCat) ⟶ _).app (op V) gs) y := by
  let := ptsModObj F r P act hnat hone hmul
  refine (yonedaEquiv_comp _ _).trans ?_
  refine (actHomF_left_app F r P act hnat _ _ _ V _).trans ?_
  congr 1
  · change yonedaEquiv ((smulSectionLift (ptsGS F r).obj.X (overBaseS P) gs y h ≫
      pullback.fst (ptsGS F r).obj.X.hom (overBaseS P).hom) ≫ prod.snd) = _
    rw [smulSectionLift_fst]
    exact (yonedaEquiv_comp (yonedaEquiv.symm gs) prod.snd).trans
      (congrArg _ (Equiv.apply_symm_apply _ _))
  · change yonedaEquiv (smulSectionLift (ptsGS F r).obj.X (overBaseS P) gs y h ≫
      pullback.snd (ptsGS F r).obj.X.hom (overBaseS P).hom) = _
    rw [smulSectionLift_snd, Equiv.apply_symm_apply]

end PointsAction

/-! ### Points of a base change of a group algebraic space -/

section BaseChangePoints

variable {B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} {hB : IsAlgebraicSpace 𝒞 S hS B}
  (Gr : GroupAlgebraicSpace 𝒞 S hS B hB)

/-- The morphism of presheaves `W ⟶ U ×_{b, ℬ} 𝒢` underlying a point of `G_U` over a test
object `W` of `(Sch/U)_fppf`. -/
abbrev pbLeft {U : BigFppfOver 𝒞 S hS} {b : yoneda.obj U ⟶ B} {W : Over U}
    (k : sliceOver W ⟶ (pullbackGroup hB Gr U b).obj.X) :
    yoneda.obj W.left ⟶ pullback Gr.obj.X.hom b :=
  k.left

/-- The component in `U` of a point of `G_U` over `W` is the structure morphism of `W`. -/
theorem pbLeft_snd {U : BigFppfOver 𝒞 S hS} {b : yoneda.obj U ⟶ B} {W : Over U}
    (k : sliceOver W ⟶ (pullbackGroup hB Gr U b).obj.X) :
    pbLeft Gr k ≫ pullback.snd Gr.obj.X.hom b = yoneda.map W.hom :=
  Over.w k

/-- The component in `𝒢` of a point of `G_U` over `W` lies over `ℬ` via the composite of the
structure morphism of `W` with `b`. -/
theorem pbLeft_fst_w {U : BigFppfOver 𝒞 S hS} {b : yoneda.obj U ⟶ B} {W : Over U}
    (k : sliceOver W ⟶ (pullbackGroup hB Gr U b).obj.X) :
    (pbLeft Gr k ≫ pullback.fst Gr.obj.X.hom b) ≫ Gr.obj.X.hom = yoneda.map W.hom ≫ b := by
  rw [Category.assoc, pullback.condition, ← Category.assoc, pbLeft_snd]

/-- **The points of `G_U = U ×_{b, ℬ} 𝒢` over a test object `W` of `(Sch/U)_fppf` are the points
of `𝒢` over `W`**, as groups: composition with the projection `G_U ⟶ 𝒢`. -/
def baseChangePts (U : BigFppfOver 𝒞 S hS) (b : yoneda.obj U ⟶ B) (W : Over U) :
    (sliceOver W ⟶ (pullbackGroup hB Gr U b).obj.X) ≃*
      ((Over.mk (yoneda.map W.hom ≫ b) : Over B) ⟶ Gr.obj.X) where
  toFun k := Over.homMk (pbLeft Gr k ≫ pullback.fst Gr.obj.X.hom b) (pbLeft_fst_w Gr k)
  invFun m := Over.homMk (pullback.lift m.left (yoneda.map W.hom) (Over.w m))
    (pullback.lift_snd _ _ _)
  left_inv k := by
    refine Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans (pbLeft_snd Gr k).symm
  right_inv m := Over.OverMorphism.ext (pullback.lift_fst _ _ _)
  map_mul' k k' := by
    let P : Over (yoneda.obj U) := (pullbackGroup hB Gr U b).obj.X
    let DB : Over B := Over.mk ((P ⊗ P).hom ≫ b)
    let PB : Over B := Over.mk (P.hom ≫ b)
    let proj : PB ⟶ Gr.obj.X := Over.homMk (pullback.fst Gr.obj.X.hom b) pullback.condition
    let mulHom : DB ⟶ PB := Over.homMk (μ[P]).left (by
      change (μ[P]).left ≫ P.hom ≫ b = (P ⊗ P).hom ≫ b
      rw [← Category.assoc, (μ[P]).w])
    let fstHom : DB ⟶ PB :=
      Over.homMk (pullback.fst P.hom P.hom) (Category.assoc _ _ _).symm
    let sndHom : DB ⟶ PB := Over.homMk (pullback.snd P.hom P.hom) (by
      change pullback.snd P.hom P.hom ≫ P.hom ≫ b = pullback.fst P.hom P.hom ≫ P.hom ≫ b
      rw [← Category.assoc, ← pullback.condition, Category.assoc])
    have hmul : mulHom ≫ proj = (fstHom ≫ proj) * (sndHom ≫ proj) :=
      Over.OverMorphism.ext (pullbackGroup_mul_left_comp_fst hB Gr U b)
    let L : (Over.mk (yoneda.map W.hom ≫ b) : Over B) ⟶ DB :=
      Over.homMk (CartesianMonoidalCategory.lift k k').left (by
        change (CartesianMonoidalCategory.lift k k').left ≫ (P ⊗ P).hom ≫ b = _
        rw [← Category.assoc, (CartesianMonoidalCategory.lift k k').w]
        rfl)
    have e1 : (Over.homMk (pbLeft Gr (k * k') ≫ pullback.fst Gr.obj.X.hom b)
        (pbLeft_fst_w Gr (k * k')) : (Over.mk (yoneda.map W.hom ≫ b) : Over B) ⟶ Gr.obj.X) =
        L ≫ mulHom ≫ proj := Over.OverMorphism.ext (Category.assoc _ _ _)
    have e2 : (Over.homMk (pbLeft Gr k ≫ pullback.fst Gr.obj.X.hom b)
        (pbLeft_fst_w Gr k) : (Over.mk (yoneda.map W.hom ≫ b) : Over B) ⟶ Gr.obj.X) =
        L ≫ fstHom ≫ proj := Over.OverMorphism.ext (by
      change _ = (CartesianMonoidalCategory.lift k k').left ≫ pullback.fst P.hom P.hom ≫ _
      rw [← Category.assoc]
      exact congrArg (· ≫ pullback.fst Gr.obj.X.hom b)
        (congrArg Over.Hom.left (CartesianMonoidalCategory.lift_fst k k')).symm)
    have e3 : (Over.homMk (pbLeft Gr k' ≫ pullback.fst Gr.obj.X.hom b)
        (pbLeft_fst_w Gr k') : (Over.mk (yoneda.map W.hom ≫ b) : Over B) ⟶ Gr.obj.X) =
        L ≫ sndHom ≫ proj := Over.OverMorphism.ext (by
      change _ = (CartesianMonoidalCategory.lift k k').left ≫ pullback.snd P.hom P.hom ≫ _
      rw [← Category.assoc]
      exact congrArg (· ≫ pullback.fst Gr.obj.X.hom b)
        (congrArg Over.Hom.left (CartesianMonoidalCategory.lift_snd k k')).symm)
    refine e1.trans ((congrArg (L ≫ ·) hmul).trans ((MonObj.comp_mul _ _ _).trans ?_))
    rw [← e2, ← e3]

/-- `baseChangePts` is composition with the projection `G_U ⟶ 𝒢`. -/
theorem baseChangePts_apply_left (U : BigFppfOver 𝒞 S hS) (b : yoneda.obj U ⟶ B) (W : Over U)
    (k : sliceOver W ⟶ (pullbackGroup hB Gr U b).obj.X) :
    (baseChangePts Gr U b W k).left = pbLeft Gr k ≫ pullback.fst Gr.obj.X.hom b :=
  rfl

/-- The inverse of `baseChangePts` pairs a point of `𝒢` with the structure morphism of `W`. -/
theorem baseChangePts_symm_apply_left (U : BigFppfOver 𝒞 S hS) (b : yoneda.obj U ⟶ B)
    (W : Over U) (m : (Over.mk (yoneda.map W.hom ≫ b) : Over B) ⟶ Gr.obj.X) :
    ((baseChangePts Gr U b W).symm m).left =
      pullback.lift m.left (yoneda.map W.hom) (Over.w m) :=
  rfl

end BaseChangePoints

/-! ### The identification of `G_U` with the constant sheaf of groups -/

section ConstantData

variable (F : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ GrpCat.{u}) {a₀ : BigFppfOver 𝒞 S hS}
  (r : (F ⋙ forget GrpCat).RepresentableBy a₀)

/-- The point of `ptsGS F r` attached to a section `y` of `F` has component `y` in the
presheaf of points. -/
theorem pointsMulEquiv_symm_left_snd {T : BigFppfOver 𝒞 S hS} (β : yoneda.obj T ⟶ baseS 𝒞 S hS)
    (y : F.obj (op T)) :
    ((GroupAlgebraicSpace.pointsMulEquiv 𝒞 S hS (baseS 𝒞 S hS) F T β).symm y).left ≫
      prod.snd = yonedaEquiv.symm y := by
  apply yonedaEquiv.injective
  rw [Equiv.apply_symm_apply, ← GroupAlgebraicSpace.pointsMulEquiv_apply, MulEquiv.apply_symm_apply]

variable [HasWeakSheafify (BigFppfOver.topology 𝒞 S hS) GrpCat.{max (u + 1) v}]
  (φ : ∀ T : BigFppfOver 𝒞 S hS,
    (constantSheafOfGroups (BigFppfOver.topology 𝒞 S hS) G).presheaf.obj (op T) ≃* F.obj (op T))

/-- The points of `G_U` over a test object `W` of `(Sch/U)_fppf` attached to a section of the
constant sheaf of groups through `φ`. -/
def constPt (U : BigFppfOver 𝒞 S hS) (b : yoneda.obj U ⟶ baseS 𝒞 S hS) (W : Over U) :
    (constantSheafOfGroups (BigFppfOver.topology 𝒞 S hS) G).presheaf.obj (op W.left) ≃*
      (sliceOver W ⟶ (pullbackGroup (isAlgebraicSpace_baseS 𝒞 S hS) (ptsGS F r) U b).obj.X) :=
  ((φ W.left).trans (GroupAlgebraicSpace.pointsMulEquiv 𝒞 S hS (baseS 𝒞 S hS) F W.left
    (yoneda.map W.hom ≫ b)).symm).trans (baseChangePts (ptsGS F r) U b W).symm

omit [Small.{u} G] in
/-- The point of `G_U` attached to a section `g` of the constant sheaf has component `φ g` in
the presheaf of points. -/
theorem constPt_left_fst_snd (U : BigFppfOver 𝒞 S hS) (b : yoneda.obj U ⟶ baseS 𝒞 S hS)
    (W : Over U) (g : (constantSheafOfGroups (BigFppfOver.topology 𝒞 S hS) G).presheaf.obj
      (op W.left)) :
    pbLeft (ptsGS F r) (constPt F r φ U b W g) ≫ pullback.fst _ b ≫ prod.snd =
      yonedaEquiv.symm (φ W.left g) :=
  (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ prod.snd) (pullback.lift_fst _ _ _)).trans
    (pointsMulEquiv_symm_left_snd F _ _))

omit [Small.{u} G] in
/-- The point of `G_U` attached to a section of the constant sheaf has component in `U` the
structure morphism of `W`. -/
theorem constPt_left_snd (U : BigFppfOver 𝒞 S hS) (b : yoneda.obj U ⟶ baseS 𝒞 S hS)
    (W : Over U) (g : (constantSheafOfGroups (BigFppfOver.topology 𝒞 S hS) G).presheaf.obj
      (op W.left)) :
    pbLeft (ptsGS F r) (constPt F r φ U b W g) ≫ pullback.snd _ b = yoneda.map W.hom :=
  pbLeft_snd _ _

omit [HasWeakSheafify (BigFppfOver.topology 𝒞 S hS) GrpCat] in
/-- Two morphisms into `G_U` agree as soon as their components in the presheaf of points and in
`U` agree. -/
theorem pbLeft_ext {U : BigFppfOver 𝒞 S hS} {b : yoneda.obj U ⟶ baseS 𝒞 S hS}
    {T : BigFppfOver 𝒞 S hS}
    {f g : yoneda.obj T ⟶ pullback (ptsGS F r).obj.X.hom b}
    (h₁ : f ≫ pullback.fst _ b ≫ prod.snd = g ≫ pullback.fst _ b ≫ prod.snd)
    (h₂ : f ≫ pullback.snd _ b = g ≫ pullback.snd _ b) : f = g := by
  refine pullback.hom_ext (prod.hom_ext (baseS_ext _ _) ?_) h₂
  exact (Category.assoc _ _ _).trans (h₁.trans (Category.assoc _ _ _).symm)

variable (hφ : ∀ {T T' : BigFppfOver 𝒞 S hS} (f : T' ⟶ T)
    (g : (constantSheafOfGroups (BigFppfOver.topology 𝒞 S hS) G).presheaf.obj (op T)),
    φ T' ((constantSheafOfGroups (BigFppfOver.topology 𝒞 S hS) G).presheaf.map f.op g) =
      (F ⋙ forget GrpCat).map f.op (φ T g))

include hφ in
omit [Small.{u} G] in
/-- If `φ` is natural, then `constPt` commutes with restriction along morphisms over `U`. -/
theorem constPt_map (U : BigFppfOver 𝒞 S hS) (b : yoneda.obj U ⟶ baseS 𝒞 S hS)
    {V W : Over U} (f : W ⟶ V)
    (g : (constantSheafOfGroups (BigFppfOver.topology 𝒞 S hS) G).presheaf.obj (op V.left)) :
    constPt F r φ U b W
        ((constantSheafOfGroups (BigFppfOver.topology 𝒞 S hS) G).presheaf.map f.left.op g) =
      sliceRestrict f ≫ constPt F r φ U b V g := by
  refine Over.OverMorphism.ext (pbLeft_ext F r ?_ ?_)
  · refine (constPt_left_fst_snd F r φ U b W _).trans ?_
    rw [hφ, ← yonedaEquiv_symm_naturality_left]
    exact congrArg (yoneda.map f.left ≫ ·) (constPt_left_fst_snd F r φ U b V g).symm
  · refine (constPt_left_snd F r φ U b W _).trans ?_
    refine Eq.trans ?_ (congrArg (yoneda.map f.left ≫ ·) (constPt_left_snd F r φ U b V g)).symm
    rw [← Functor.map_comp, Over.w f]

/-- **The identification of `G_U` with the constant sheaf of groups**, for the group algebraic
space whose points are the sections of `F`, given an identification `φ` of the sections of
`F` with those of the constant sheaf of groups. -/
def constData : ConstantGroupData (isAlgebraicSpace_baseS 𝒞 S hS) (ptsGS F r) G where
  equiv U b :=
    { equiv W := (constPt F r φ U b W.unop).toEquiv.trans (sliceSectionEquiv _ W.unop)
      map_mul W g h := by
        have e := map_mul (constPt F r φ U b W.unop) g h
        refine (congrArg (sliceSectionEquiv _ W.unop) e).trans ?_
        rw [sliceSheafOfGroups_mul]
        exact congrArg (sliceSectionEquiv _ W.unop) (congrArg₂ (· * ·)
          (Equiv.symm_apply_apply _ _).symm (Equiv.symm_apply_apply _ _).symm)
      naturality {V W} f g := by
        change sliceSectionEquiv _ W.unop (constPt F r φ U b W.unop _) =
          (sliceSection _).map f (sliceSectionEquiv _ V.unop (constPt F r φ U b V.unop g))
        rw [sliceSectionEquiv_map]
        exact congrArg _ (constPt_map F r φ hφ U b f.unop g) }
  equiv_baseChange {U U' b b'} f hf W a ha gs := by
    change yonedaEquiv (pbLeft _ (constPt F r φ U' b' (Over.mk a) gs)) =
      yonedaEquiv (pbLeft _ (constPt F r φ U b W gs) ≫
        baseChangeGroupHom (isAlgebraicSpace_baseS 𝒞 S hS) (ptsGS F r) f hf)
    refine congrArg yonedaEquiv (pbLeft_ext F r ?_ ?_)
    · refine (constPt_left_fst_snd F r φ U' b' (Over.mk a) gs).trans ?_
      refine (constPt_left_fst_snd F r φ U b W gs).symm.trans ?_
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      exact congrArg (pbLeft _ (constPt F r φ U b W gs) ≫ ·)
        (baseChangeGroupHom_fst_assoc (isAlgebraicSpace_baseS 𝒞 S hS) (ptsGS F r) f hf
          prod.snd).symm
    · refine (constPt_left_snd F r φ U' b' (Over.mk a) gs).trans ?_
      refine Eq.trans ?_ (congrArg (pbLeft _ (constPt F r φ U b W gs) ≫ ·)
        (baseChangeGroupHom_snd (isAlgebraicSpace_baseS 𝒞 S hS) (ptsGS F r) f hf).symm |>.trans
          (Category.assoc _ _ _).symm)
      rw [← Category.assoc, constPt_left_snd, ← Functor.map_comp, ← ha]
      rfl

end ConstantData

/-! ### The constant group algebraic space `G_S` and its action on `X` -/

section ConstantGroup

variable [HasWeakSheafify (BigFppfOver.topology 𝒞 S hS) GrpCat.{max (u + 1) v}]

/-- The constant group algebraic space `G_S` over `S`, read as the group algebraic space whose
points are the points of the constant group scheme. It is
`AlgebraicGeometry.Space.constantGroupSpace` at the base `S` (`constGS_eq`). -/
abbrev constGS : GroupAlgebraicSpace 𝒞 S hS (baseS 𝒞 S hS) (isAlgebraicSpace_baseS 𝒞 S hS) :=
  ptsGS (constantGroupPointsOnSite 𝒞 S hS G hG)
    (pointsOnSiteRepresentableBy 𝒞 S hS _ (constantGroupSiteObjectGrpObj 𝒞 S hS G hG))

omit [HasWeakSheafify (BigFppfOver.topology 𝒞 S hS) GrpCat] in
/-- `constGS` is `AlgebraicGeometry.Space.constantGroupSpace` at the base `S`. -/
theorem constGS_eq : constGS (hS := hS) hG =
    constantGroupSpace 𝒞 S hS G (baseS 𝒞 S hS) (isAlgebraicSpace_baseS 𝒞 S hS) hG :=
  rfl

/-- The identification of the sections of the constant sheaf of groups with the points of
`G_S`, from the representation of the constant sheaf by `G_S` (the second clause of
Stacks 0371). -/
def constSheafPts (T : BigFppfOver 𝒞 S hS) :
    (constantSheafOfGroups (BigFppfOver.topology 𝒞 S hS) G).presheaf.obj (op T) ≃*
      (constantGroupPointsOnSite 𝒞 S hS G hG).obj (op T) :=
  ((constantGroupSheafRepresentedByConstantGroupScheme_bigFppf 𝒞 S hS G).2.1.app
    (op T)).groupIsoToMulEquiv.trans MulEquiv.ulift

/-- `AlgebraicGeometry.Space.constSheafPts` as a plain function. -/
def cspFun (T : BigFppfOver 𝒞 S hS)
    (g : (constantSheafOfGroups (BigFppfOver.topology 𝒞 S hS) G).presheaf.obj (op T)) :
    (constantGroupPointsOnSite 𝒞 S hS G hG).obj (op T) :=
  constSheafPts hG T g

/-- `AlgebraicGeometry.Space.cspFun` is injective. -/
theorem cspFun_injective (T : BigFppfOver 𝒞 S hS) : Function.Injective (cspFun hG T) :=
  (constSheafPts hG T).injective

/-- The identification of sections of the constant sheaf with points of `G_S` commutes with
restriction. -/
theorem constSheafPts_map {T T' : BigFppfOver 𝒞 S hS} (f : T' ⟶ T)
    (g : (constantSheafOfGroups (BigFppfOver.topology 𝒞 S hS) G).presheaf.obj (op T)) :
    cspFun hG T' ((constantSheafOfGroups (BigFppfOver.topology 𝒞 S hS) G).presheaf.map
      f.op g) = ptsRes hG f (cspFun hG T g) :=
  congrArg ULift.down (NatTrans.naturality_apply
    (constantGroupSheafRepresentedByConstantGroupScheme_bigFppf 𝒞 S hS G).2.1.hom f.op g)

/-- The constant section `g` of the constant sheaf corresponds to the point of `G_S` whose map is
constant with value `g`. -/
theorem ptFun_constSheafPts_unit (T : BigFppfOver 𝒞 S hS) (g : G) (w : sch T) :
    ptFun hG (V := T) (constSheafPts hG T
      (constantSheafOfGroupsUnit (BigFppfOver.topology 𝒞 S hS) G (op T) g)) w = g := by
  have h := (constantGroupSheafRepresentedByConstantGroupScheme_bigFppf 𝒞 S hS G).2.2 (op T) g
  exact congrArg (fun φ : LocallyConstant (sch T) G => φ w) h

/-- **The identification of `G_U = U ×_S G_S` with the constant sheaf of groups.** -/
def constGSData : ConstantGroupData (isAlgebraicSpace_baseS 𝒞 S hS) (constGS (hS := hS) hG) G :=
  constData _ _ (constSheafPts hG) (fun f g => constSheafPts_map hG f g)

/-- **The action of `G_S` on `X` induced by the action `ρ` of `G`.** -/
@[reducible]
def constGSModObj : ModObj (constGS (hS := hS) hG).obj.X (overBaseS X₀) :=
  ptsModObj _ _ X₀ (fun _ gp x => actGlue hG hX₀ ρ₀ gp x)
    (fun h gp x => actGlue_naturality hG hX₀ ρ₀ h gp x)
    (fun _ x => actGlue_one hG hX₀ ρ₀ x) (fun _ a b x => actGlue_mul hG hX₀ ρ₀ a b x)

/-- The action `ρ` of `G` on `X`, carried to the universe lift of `X`. -/
abbrev uliftAction : G →* Aut (X₀ ⋙ uliftFunctor.{t}) :=
  (((Functor.whiskeringRight _ _ _).obj uliftFunctor.{t}).mapAut X₀).comp ρ₀

/-- **The compatibility of the two actions**: the constant section `g` of `G_S` acts on `X` as
`ρ g` does. -/
theorem constGS_isCompatibleAction :
    letI := constGSModObj hG hX₀ ρ₀
    IsCompatibleAction (X := overBaseS X₀) (constGSData hG) (uliftAction.{t} ρ₀) := by
  intro V β g x hx
  refine (ptsModObj_smulSection (constantGroupPointsOnSite 𝒞 S hS G hG)
    (pointsOnSiteRepresentableBy 𝒞 S hS _ (constantGroupSiteObjectGrpObj 𝒞 S hS G hG)) X₀
    (fun V gp x => actGlue hG hX₀ ρ₀ gp x)
    (fun h gp x => actGlue_naturality hG hX₀ ρ₀ h gp x)
    (fun V x => actGlue_one hG hX₀ ρ₀ x) (fun V a b x => actGlue_mul hG hX₀ ρ₀ a b x)
    ((constGSData hG).constSection V β g) x _).trans ?_
  have e := constPt_left_fst_snd _
    (pointsOnSiteRepresentableBy 𝒞 S hS _ (constantGroupSiteObjectGrpObj 𝒞 S hS G hG))
    (constSheafPts hG) V β (Over.mk (𝟙 V))
    (constantSheafOfGroupsUnit (BigFppfOver.topology 𝒞 S hS) G (op V) g)
  refine (congrArg (fun gp => actGlue hG hX₀ ρ₀ (V := V) gp x)
    ((congrArg yonedaEquiv e).trans (Equiv.apply_symm_apply _ _))).trans ?_
  exact actGlue_of_const hG hX₀ ρ₀ _ x g (ptFun_constSheafPts_unit hG V g)

end ConstantGroup

end AlgebraicGeometry.Space
