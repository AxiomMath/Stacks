module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.PointwiseFibrationModules
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.StackificationModulesSmall

/-!
# Modules on the pointwise groupoid fibration are descent data on the object space

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces and let `P = [U/_pR]` be its pointwise
groupoid fibration.  Restricting a module `N` on `P` to the category of the object space `𝒮_U`
and recording the restriction maps of `N` along the morphisms of `P` over identities gives a
descent datum `(N|_{𝒮_U}, β)` (`AlgebraicGeometry.Stack.PointwiseDescentDatum`).  This file
proves that this is an equivalence of categories, and that it matches quasi-coherent modules
with descent data whose underlying module is quasi-coherent.

## Main definitions

* `AlgebraicGeometry.Stack.restrictionDatum`: the descent datum of a module on `P`.
* `AlgebraicGeometry.Stack.descentRestriction`: the functor from modules on `P` to descent data.
* `AlgebraicGeometry.Stack.PointwiseDescentDatum.sheaf`: the module on `P` glued from a descent
  datum.
* `AlgebraicGeometry.Stack.pointwiseDescentEquivalence`: `Mod(𝒪_P) ≌` descent data.
* `AlgebraicGeometry.Stack.pointwiseQuasicoherentEquivalence`: `QCoh(𝒪_P) ≌` descent data whose
  underlying module on `𝒮_U` is quasi-coherent.

## Main results

* `AlgebraicGeometry.Stack.isEquivalence_descentRestriction`: the restriction to descent data is
  an equivalence of categories.
* `AlgebraicGeometry.Stack.isQuasicoherentOnSite_objectRestriction_iff`: a module on `P` is
  quasi-coherent if and only if its restriction to `𝒮_U` is.

## Implementation notes

The restriction of `N` to `𝒮_U` has the same sections as `N`, but its type is an inverse image
of modules, and equations whose two sides differ only by unfolding that inverse image are
expensive to check.  The proofs below therefore state such equations with both sides in terms
of `N`, and compare morphisms through their underlying abelian presheaves, elementwise.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack

universe u

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)

/-- **The morphism over the identity attached to a composite arrow is the composite of the
morphisms attached to the two arrows**, up to the transports along the equalities of points. -/
theorem vertHom_compose (T : BigFppfOver C S hS) (a b : G.arrows.obj.obj (op T))
    (h : G.source.hom.app (op T) a = G.target.hom.app (op T) b) :
    vertHom G T (G.toGroupoidInFunctors.compose (op T) a b h) rfl rfl =
      eqToHom (congrArg (fun z => (⟨T, z⟩ : PointwiseFibration G)) (source_compose G T a b h)) ≫
        vertHom G T b rfl rfl ≫
          eqToHom (congrArg (fun z => (⟨T, z⟩ : PointwiseFibration G)) h.symm) ≫
            vertHom G T a rfl rfl ≫
              eqToHom (congrArg (fun z => (⟨T, z⟩ : PointwiseFibration G))
                (target_compose G T a b h).symm) := by
  symm
  refine (whisker_eq _ (whisker_eq _ (whisker_eq _ (vertHom_comp_eqToHom G T
    (target_compose G T a b h).symm a rfl rfl)))).trans ?_
  refine (whisker_eq _ (whisker_eq _ (eqToHom_comp_vertHom G T h.symm a rfl
    (target_compose G T a b h).symm))).trans ?_
  refine (whisker_eq _ (vertHom_comp_vertHom G T b a rfl rfl h (target_compose G T a b h).symm
    (source_compose G T a b h) rfl)).trans ?_
  exact eqToHom_comp_vertHom G T (source_compose G T a b h) _ _ _

variable {G}

/-- Restriction maps of a module on the pointwise groupoid fibration along a composite. -/
theorem pointwise_map_comp_op (N : SheafOfModules.{u} (pointwiseRing G))
    {x y z : PointwiseFibration G} (f : x ⟶ y) (g : y ⟶ z) :
    N.val.presheaf.map (f ≫ g).op = N.val.presheaf.map g.op ≫ N.val.presheaf.map f.op := by
  rw [op_comp, Functor.map_comp]

/-- Restriction maps of a module on the pointwise groupoid fibration along a five-fold
composite. -/
theorem pointwise_map_eq_comp₅ (N : SheafOfModules.{u} (pointwiseRing G))
    {x₀ x₁ x₂ x₃ x₄ x₅ : PointwiseFibration G} (f₁ : x₀ ⟶ x₁) (f₂ : x₁ ⟶ x₂) (f₃ : x₂ ⟶ x₃)
    (f₄ : x₃ ⟶ x₄) (f₅ : x₄ ⟶ x₅) (k : x₀ ⟶ x₅) (hk : k = f₁ ≫ f₂ ≫ f₃ ≫ f₄ ≫ f₅) :
    N.val.presheaf.map k.op = N.val.presheaf.map f₅.op ≫ N.val.presheaf.map f₄.op ≫
      N.val.presheaf.map f₃.op ≫ N.val.presheaf.map f₂.op ≫ N.val.presheaf.map f₁.op := by
  subst hk
  simp only [pointwise_map_comp_op, Category.assoc]

/-- The cocycle condition for the descent morphism of the restriction of a module on the
pointwise groupoid fibration, for an arrow `c` whose morphism over the identity is the composite
of those of `b` and `a`. -/
theorem descComp_restrictionTransition_of_eq (N : SheafOfModules.{u} (pointwiseRing G))
    (T : BigFppfOver C S hS) (a b c : G.arrows.obj.obj (op T))
    (h : G.source.hom.app (op T) a = G.target.hom.app (op T) b)
    (hsc : G.source.hom.app (op T) c = G.source.hom.app (op T) b)
    (htc : G.target.hom.app (op T) c = G.target.hom.app (op T) a)
    (hv : vertHom G T c rfl rfl =
      eqToHom (congrArg (fun z => (⟨T, z⟩ : PointwiseFibration G)) hsc) ≫
        vertHom G T b rfl rfl ≫
          eqToHom (congrArg (fun z => (⟨T, z⟩ : PointwiseFibration G)) h.symm) ≫
            vertHom G T a rfl rfl ≫
              eqToHom (congrArg (fun z => (⟨T, z⟩ : PointwiseFibration G)) htc.symm)) :
    descComp (restrictionTransition G N) T c =
      ptTransport ((objectRestriction G).obj N) htc.symm ≫
        descComp (restrictionTransition G N) T a ≫
        ptTransport ((objectRestriction G).obj N) h.symm ≫
          descComp (restrictionTransition G N) T b ≫
            ptTransport ((objectRestriction G).obj N) hsc := by
  rw [descComp_restrictionTransition, descComp_restrictionTransition,
    descComp_restrictionTransition, ptTransport_objectRestriction, ptTransport_objectRestriction,
    ptTransport_objectRestriction]
  refine (pointwise_map_eq_comp₅ N _ _ _ _ _ _ hv).trans ?_
  rfl

/-- **The descent datum of a module on the pointwise groupoid fibration**: its restriction to the
object space, with the restriction maps along the morphisms over identities. -/
def restrictionDatum (N : SheafOfModules.{u} (pointwiseRing G)) : PointwiseDescentDatum G where
  M := (objectRestriction G).obj N
  β := restrictionTransition G N
  unit T a := by
    refine (descComp_restrictionTransition N T _).trans ?_
    refine Eq.trans ?_ (ptTransport_objectRestriction N _).symm
    exact congrArg (fun k => N.val.presheaf.map k.op)
      (vertHom_identity G T a _ _ ((source_identity G T a).trans (target_identity G T a).symm))
  cocycle T a b h := descComp_restrictionTransition_of_eq N T a b _ h (source_compose G T a b h)
    (target_compose G T a b h) (vertHom_compose G T a b h)

/-! ### Morphisms of descent data on `T`-points -/

/-- The component at an object of the category of the object space of a morphism of modules
on it, as a morphism of abelian groups. -/
abbrev objComp {M M' : SheafOfModules.{u} (objRing G)} (φ : M ⟶ M') (X : ObjFib G) :
    M.val.presheaf.obj (op X) ⟶ M'.val.presheaf.obj (op X) :=
  ((PresheafOfModules.toPresheaf _).map φ.val).app (op X)

namespace PointwiseDescentDatum

/-- **A morphism of descent data commutes with the components of the descent morphisms.** -/
theorem Hom.descComp_comm {D D' : PointwiseDescentDatum G} (f : D ⟶ D') (T : BigFppfOver C S hS)
    (r : G.arrows.obj.obj (op T)) :
    descComp D.β T r ≫ objComp f.hom (objPt G T (G.source.hom.app (op T) r)) =
      objComp f.hom (objPt G T (G.target.hom.app (op T) r)) ≫ descComp D'.β T r := by
  have := congrArg (fun k => ((PresheafOfModules.toPresheaf _).map k.val).app
    (op (⟨T, ⟨r⟩⟩ : (fibredCategory C S hS G.arrows.obj).val.obj))) f.comm
  simp only [SheafOfModules.comp_val] at this
  exact this

/-- A morphism of the underlying modules commuting with the components of the descent morphisms
at every `T`-point of `R` is a morphism of descent data. -/
def homMk {D D' : PointwiseDescentDatum G} (φ : D.M ⟶ D'.M)
    (h : ∀ (T : BigFppfOver C S hS) (r : G.arrows.obj.obj (op T)),
      descComp D.β T r ≫ objComp φ (objPt G T (G.source.hom.app (op T) r)) =
        objComp φ (objPt G T (G.target.hom.app (op T) r)) ≫ descComp D'.β T r) :
    D ⟶ D' where
  hom := φ
  comm := by
    apply SheafOfModules.hom_ext
    apply (PresheafOfModules.toPresheaf _).map_injective
    refine NatTrans.ext (funext fun X => ?_)
    rcases X with ⟨⟨T, ⟨r⟩⟩⟩
    simp only [SheafOfModules.comp_val, Functor.map_comp, NatTrans.comp_app]
    exact h T r

/-- The underlying morphism of modules of `PointwiseDescentDatum.homMk`. -/
@[simp]
theorem homMk_hom {D D' : PointwiseDescentDatum G} (φ : D.M ⟶ D'.M) (h) :
    (homMk φ h).hom = φ := rfl

end PointwiseDescentDatum

/-! ### The functor from modules on the pointwise fibration to descent data -/

variable (G) in
/-- **Restriction of modules on the pointwise groupoid fibration to descent data on the object
space.** -/
def descentRestriction : SheafOfModules.{u} (pointwiseRing G) ⥤ PointwiseDescentDatum G where
  obj := restrictionDatum
  map {N N'} φ := PointwiseDescentDatum.homMk ((objectRestriction G).map φ) (fun T r => by
    refine (eq_whisker (descComp_restrictionTransition N T r) _).trans ?_
    refine Eq.trans ?_ (whisker_eq _ (descComp_restrictionTransition N' T r)).symm
    exact ((PresheafOfModules.toPresheaf _).map φ.val).naturality (vertHom G T r rfl rfl).op)
  map_id N := PointwiseDescentDatum.hom_ext ((objectRestriction G).map_id N)
  map_comp φ ψ := PointwiseDescentDatum.hom_ext ((objectRestriction G).map_comp φ ψ)

/-- The underlying module of the descent datum of a module is its restriction. -/
@[simp]
theorem descentRestriction_obj_M (N : SheafOfModules.{u} (pointwiseRing G)) :
    ((descentRestriction G).obj N).M = (objectRestriction G).obj N := rfl

/-- The underlying morphism of the morphism of descent data of a morphism of modules is its
restriction. -/
@[simp]
theorem descentRestriction_map_hom {N N' : SheafOfModules.{u} (pointwiseRing G)} (φ : N ⟶ N') :
    ((descentRestriction G).map φ).hom = (objectRestriction G).map φ := rfl

/-! ### Full faithfulness -/

/-- A family of maps between the sections of two modules on the pointwise groupoid fibration
which is natural along two composable morphisms is natural along their composite. -/
theorem pointwise_naturality_comp {N N' : SheafOfModules.{u} (pointwiseRing G)}
    (α : ∀ x : PointwiseFibration G, N.val.presheaf.obj (op x) ⟶ N'.val.presheaf.obj (op x))
    {x y z : PointwiseFibration G} (f : x ⟶ y) (g : y ⟶ z) (m : x ⟶ z) (hm : f ≫ g = m)
    (hf : N.val.presheaf.map f.op ≫ α x = α y ≫ N'.val.presheaf.map f.op)
    (hg : N.val.presheaf.map g.op ≫ α y = α z ≫ N'.val.presheaf.map g.op) :
    N.val.presheaf.map m.op ≫ α x = α z ≫ N'.val.presheaf.map m.op := by
  subst hm
  rw [pointwise_map_comp_op, pointwise_map_comp_op, Category.assoc, hf, ← Category.assoc, hg,
    Category.assoc]

/-- **A family of maps between the sections of two modules on the pointwise groupoid fibration
is natural as soon as it is natural along the images of the morphisms of the object space and
along the morphisms over identities**, since every morphism is a composite of two such
(`AlgebraicGeometry.Stack.vertHom_comp_objHom`). -/
theorem pointwise_naturality {N N' : SheafOfModules.{u} (pointwiseRing G)}
    (α : ∀ x : PointwiseFibration G, N.val.presheaf.obj (op x) ⟶ N'.val.presheaf.obj (op x))
    (h₁ : ∀ {X Y : ObjFib G} (g : X ⟶ Y),
      N.val.presheaf.map ((pointwiseObjectInclusion G).map g).op ≫ α _ =
        α _ ≫ N'.val.presheaf.map ((pointwiseObjectInclusion G).map g).op)
    (h₂ : ∀ (T : BigFppfOver C S hS) {a b : G.objects.obj.obj (op T)}
      (r : G.arrows.obj.obj (op T)) (hs : G.source.hom.app (op T) r = a)
      (ht : G.target.hom.app (op T) r = b),
      N.val.presheaf.map (vertHom G T r hs ht).op ≫ α ⟨T, a⟩ =
        α ⟨T, b⟩ ≫ N'.val.presheaf.map (vertHom G T r hs ht).op)
    {x y : PointwiseFibration G} (m : x ⟶ y) :
    N.val.presheaf.map m.op ≫ α x = α y ≫ N'.val.presheaf.map m.op :=
  pointwise_naturality_comp α _ _ m (vertHom_comp_objHom G m) (h₂ _ _ _ _) (h₁ _)

/-- The restriction to descent data is faithful: the object space has the same objects as the
pointwise fibration. -/
instance : (descentRestriction G).Faithful where
  map_injective {N N'} {φ ψ} h := by
    have h' : (objectRestriction G).map φ = (objectRestriction G).map ψ :=
      congrArg PointwiseDescentDatum.Hom.hom h
    apply SheafOfModules.hom_ext
    apply (PresheafOfModules.toPresheaf _).map_injective
    refine NatTrans.ext (funext fun x => ?_)
    exact congrArg (fun k => objComp k (objPt G x.unop.base x.unop.fiber)) h'

/-- The components of a morphism between the restrictions of two modules on the pointwise
groupoid fibration are natural along the images of the morphisms of the object space. -/
theorem objComp_objectRestriction_naturality {N N' : SheafOfModules.{u} (pointwiseRing G)}
    (φ : (objectRestriction G).obj N ⟶ (objectRestriction G).obj N') {X Y : ObjFib G}
    (g : X ⟶ Y) :
    N.val.presheaf.map ((pointwiseObjectInclusion G).map g).op ≫ objComp φ X =
      objComp φ Y ≫ N'.val.presheaf.map ((pointwiseObjectInclusion G).map g).op :=
  ((PresheafOfModules.toPresheaf _).map φ.val).naturality g.op

/-- The morphism of modules on the pointwise groupoid fibration attached to a morphism of their
descent data: on sections over `(T, a)` it is the component of the morphism of modules on the
object space. -/
def descentRestrictionPreimage {N N' : SheafOfModules.{u} (pointwiseRing G)}
    (f : (descentRestriction G).obj N ⟶ (descentRestriction G).obj N') : N ⟶ N' :=
  ⟨PresheafOfModules.homMk
    { app := fun x => objComp f.hom (objPt G x.unop.base x.unop.fiber)
      naturality := fun _ _ m => pointwise_naturality
        (fun x => objComp f.hom (objPt G x.base x.fiber))
        (fun {X Y} g => by
          rcases X with ⟨T, ⟨a⟩⟩
          rcases Y with ⟨T', ⟨a'⟩⟩
          exact objComp_objectRestriction_naturality f.hom g)
        (fun T _ _ r hs ht => by
          subst hs ht
          exact (eq_whisker (descComp_restrictionTransition N T r) _).symm.trans
            ((f.descComp_comm T r).trans (whisker_eq _ (descComp_restrictionTransition N' T r))))
        m.unop }
    (fun X c m => (f.hom.val.app (op (objPt G X.unop.base X.unop.fiber))).hom.map_smul c m)⟩

/-- The morphism of modules attached to a morphism of descent data restricts to it. -/
theorem descentRestriction_map_preimage {N N' : SheafOfModules.{u} (pointwiseRing G)}
    (f : (descentRestriction G).obj N ⟶ (descentRestriction G).obj N') :
    (descentRestriction G).map (descentRestrictionPreimage f) = f := by
  apply PointwiseDescentDatum.hom_ext
  apply SheafOfModules.hom_ext
  apply (PresheafOfModules.toPresheaf _).map_injective
  exact NatTrans.ext (funext fun X => AddCommGrpCat.ext fun m => rfl)

/-- The restriction to descent data is full. -/
instance : (descentRestriction G).Full where
  map_surjective f := ⟨descentRestrictionPreimage f, descentRestriction_map_preimage f⟩

/-! ### Essential surjectivity -/

/-- The restriction map of the glued module of a descent datum along the morphism over the
identity attached to a `T`-point `r` of `R` is the component of the descent morphism at `r`. -/
theorem glueMap_vertHom (D : PointwiseDescentDatum G) (T : BigFppfOver C S hS)
    (r : G.arrows.obj.obj (op T)) : glueMap D (vertHom G T r rfl rfl) = descComp D.β T r := by
  unfold glueMap
  refine (descStep_congr D.β (𝟙 T) _ _ (pointwiseArrow_vertHom G T r rfl rfl) _ _
    (G.objects.obj.map_id_apply _ _) rfl).trans ?_
  unfold descStep
  rw [map_objHom_id, ptTransport_rfl, ptTransport_rfl, Category.id_comp, Category.comp_id]

/-- The sheaf of modules on the pointwise groupoid fibration glued from a descent datum. -/
def PointwiseDescentDatum.sheaf (D : PointwiseDescentDatum G) :
    SheafOfModules.{u} (pointwiseRing G) :=
  ⟨D.presheafOfModules, D.isSheaf_presheaf⟩

/-- The descent morphism of the restriction of the glued module of a descent datum is the
descent morphism of the datum, componentwise. -/
theorem descComp_restrictionTransition_sheaf (D : PointwiseDescentDatum G)
    (T : BigFppfOver C S hS) (r : G.arrows.obj.obj (op T)) :
    descComp (restrictionTransition G D.sheaf) T r = descComp D.β T r :=
  (descComp_restrictionTransition D.sheaf T r).trans (glueMap_vertHom D T r)

/-- The restriction to the object space of the glued module of a descent datum, on underlying
abelian presheaves. -/
def PointwiseDescentDatum.sheafRestrictionIsoAb (D : PointwiseDescentDatum G) :
    ((objectRestriction G).obj D.sheaf).val.presheaf ≅ D.M.val.presheaf :=
  NatIso.ofComponents (fun X => Iso.refl _) (fun {X Y} g => by
    simp only [Iso.refl_hom]
    exact glueMap_pointwiseObjectInclusion D g.unop)

/-- **The restriction to the object space of the glued module of a descent datum is the
underlying module of the descent datum.** -/
def PointwiseDescentDatum.sheafRestrictionIso (D : PointwiseDescentDatum G) :
    (objectRestriction G).obj D.sheaf ≅ D.M where
  hom := ⟨PresheafOfModules.homMk D.sheafRestrictionIsoAb.hom (fun _ _ _ => rfl)⟩
  inv := ⟨PresheafOfModules.homMk D.sheafRestrictionIsoAb.inv (fun _ _ _ => rfl)⟩
  hom_inv_id := by
    apply SheafOfModules.hom_ext
    apply (PresheafOfModules.toPresheaf _).map_injective
    exact NatTrans.ext (funext fun X => AddCommGrpCat.ext fun m => rfl)
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    apply (PresheafOfModules.toPresheaf _).map_injective
    exact NatTrans.ext (funext fun X => AddCommGrpCat.ext fun m => rfl)

/-- **The descent datum of the glued module of a descent datum is the descent datum itself.** -/
def PointwiseDescentDatum.sheafIso (D : PointwiseDescentDatum G) :
    (descentRestriction G).obj D.sheaf ≅ D where
  hom := PointwiseDescentDatum.homMk D.sheafRestrictionIso.hom (fun T r =>
    AddCommGrpCat.ext fun m => ConcreteCategory.congr_hom
      (descComp_restrictionTransition_sheaf D T r) m)
  inv := PointwiseDescentDatum.homMk D.sheafRestrictionIso.inv (fun T r =>
    AddCommGrpCat.ext fun m => ConcreteCategory.congr_hom
      (descComp_restrictionTransition_sheaf D T r).symm m)
  hom_inv_id := PointwiseDescentDatum.hom_ext D.sheafRestrictionIso.hom_inv_id
  inv_hom_id := PointwiseDescentDatum.hom_ext D.sheafRestrictionIso.inv_hom_id

/-- Every descent datum is the descent datum of its glued module. -/
instance : (descentRestriction G).EssSurj where
  mem_essImage D := ⟨D.sheaf, ⟨D.sheafIso⟩⟩

variable (G) in
/-- **Modules on the pointwise groupoid fibration are descent data on the object space**: the
restriction functor is an equivalence of categories. -/
instance isEquivalence_descentRestriction : (descentRestriction G).IsEquivalence where

variable (G) in
/-- **The equivalence between modules on the pointwise groupoid fibration and descent data on
the object space.** -/
def pointwiseDescentEquivalence :
    SheafOfModules.{u} (pointwiseRing G) ≌ PointwiseDescentDatum G :=
  (descentRestriction G).asEquivalence

/-! ### Quasi-coherent modules -/

variable (G) in
/-- The inclusion of the object space into the pointwise groupoid fibration is cover dense: it
is surjective on objects. -/
theorem isCoverDense_pointwiseObjectInclusion :
    (pointwiseObjectInclusion G).IsCoverDense (associatedTopology C S hS
      (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p C.topology) where
  is_cover x := by
    have : Sieve.coverByImage (pointwiseObjectInclusion G) x = ⊤ :=
      (Sieve.id_mem_iff_eq_top).1 ⟨⟨objPt G x.base x.fiber, 𝟙 _, 𝟙 _, Category.id_comp _⟩⟩
    rw [this]
    exact GrothendieckTopology.top_mem _ _

/-- **A module on the pointwise groupoid fibration is quasi-coherent if and only if its
restriction to the object space is.** -/
theorem isQuasicoherentOnSite_objectRestriction_iff (N : SheafOfModules.{u} (pointwiseRing G)) :
    ((objectRestriction G).obj N).IsQuasicoherentOnSite ↔ N.IsQuasicoherentOnSite :=
  ⟨isQuasicoherentOnSite_of_modulePullback' C S hS _ _ _ _ _ _
      (isCoverDense_pointwiseObjectInclusion G) N,
    isQuasicoherentOnSite_modulePullback' C S hS _ _ _ _ _ _ N⟩

/-- Quasi-coherence of descent data is invariant under isomorphism. -/
instance : (PointwiseDescentDatum.qcoh G).IsClosedUnderIsomorphisms where
  of_iso e h := SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((PointwiseDescentDatum.forget (G := G)).mapIso e) h

variable (G) in
/-- A module on the pointwise groupoid fibration is quasi-coherent if and only if its descent
datum is quasi-coherent. -/
theorem inverseImage_descentRestriction_qcoh :
    (PointwiseDescentDatum.qcoh G).inverseImage (descentRestriction G) =
      SheafOfModules.isQuasicoherentOnSite.{_, _, u, u} (pointwiseRing G) :=
  funext fun N => propext (isQuasicoherentOnSite_objectRestriction_iff N)

variable (G) in
/-- **Quasi-coherent modules on the pointwise groupoid fibration are quasi-coherent descent data
on the object space**: the equivalence `pointwiseDescentEquivalence` restricts to an equivalence
between `QCoh(𝒪_P)` (Stacks 06WG) and the descent data whose underlying module on `𝒮_U` is
quasi-coherent. -/
def pointwiseQuasicoherentEquivalence :
    FibredSite.quasicoherentModules.{u, u + 1, u, u} C S hS
        (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p
        (isFiberedInGroupoids_presheafOfGroupoids _) ≌
      (PointwiseDescentDatum.qcoh G).FullSubcategory :=
  (pointwiseDescentEquivalence G).congrFullSubcategory (inverseImage_descentRestriction_qcoh G)

end AlgebraicGeometry.Stack

end
