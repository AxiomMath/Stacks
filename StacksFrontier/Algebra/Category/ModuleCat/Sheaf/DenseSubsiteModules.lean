module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Module.MinimalAxioms
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import StacksCore.Tactic.StacksAttribute

/-!
# The Comparison Lemma for sheaves of modules on a dense subsite

Let `v : C ⥤ C'` exhibit `(C, J)` as a dense subsite of `(C', K)`
(`CategoryTheory.Functor.IsDenseSubsite`) and let `R` be a sheaf of rings on `(C', K)`.
Restriction of sections along `v` carries `R` to a sheaf of rings `ringRestriction J K v R`
on `(C, J)` and carries a sheaf of `R`-modules to a sheaf of modules over it; this is
Mathlib's `SheafOfModules.pushforward (𝟙 _)`, written here `moduleRestriction J K v R`.

The main result is that this restriction functor is **fully faithful always**, and an
**equivalence** as soon as the Comparison Lemma holds for sheaves of abelian groups, i.e. as
soon as `v.sheafPushforwardContinuous AddCommGrpCat J K` is an equivalence, which holds
(`CategoryTheory.Functor.IsDenseSubsite.sheafPushforwardContinuous.isEquivalence`) under
`∀ X, HasLimitsOfShape (StructuredArrow X v.op) AddCommGrpCat`. No hypothesis is placed on
the sites themselves: they need not be small, have finite limits, or be iso-closed.

This is the module-level counterpart of `CategoryTheory.Functor.IsDenseSubsite.sheafEquiv`,
and is the input that Stacks' "method (2)" for proving that a property of sheaves of modules
is intrinsic to the ringed topos (Stacks 03DG) consumes. It generalizes
`Stacks.BasisRestriction.isEquivalence_restrictModuleSheaf` (Stacks 009U), which is the case
of the inclusion of a basis of opens of a topological space.

## Main definitions

* `Stacks.DenseSubsiteModules.ringRestriction`: the restriction of a sheaf of rings along `v`.
* `Stacks.DenseSubsiteModules.moduleRestriction`: the restriction of sheaves of modules.
* `Stacks.DenseSubsiteModules.extSheaf`: a sheaf of abelian groups on `(C', K)` whose
  restriction carries a module structure, equipped with the transported module structure.
* `Stacks.DenseSubsiteModules.moduleRestrictionEquivalence`: the resulting equivalence
  `SheafOfModules R ≌ SheafOfModules (ringRestriction J K v R)`, together with the instance
  `isEquivalence_moduleRestriction`.

## Main results

* `Stacks.DenseSubsiteModules.moduleRestriction_comp_toSheaf`: restriction of sheaves of
  modules is, on the nose, restriction of the underlying sheaves of abelian groups.
* the `Functor.Faithful` and `Functor.Full` instances for `moduleRestriction`: full
  faithfulness needs only the dense-subsite hypothesis.
* `Stacks.DenseSubsiteModules.essSurj_moduleRestriction`: essential surjectivity, given the
  Comparison Lemma for `AddCommGrpCat`.
* `Stacks.DenseSubsiteModules.extIso`: the restriction of `extSheaf N G ι` is `N`.
* `Stacks.DenseSubsiteModules.ringRestriction_over`,
  `Stacks.DenseSubsiteModules.pushforward_comp_overFunctor` and
  `Stacks.DenseSubsiteModules.moduleRestriction_comp_overFunctor`: **restriction along `v`
  commutes with restriction to a slice**, on sheaves of rings and on sheaves of modules. All
  three are equalities, by `rfl`.

## Implementation notes

Full faithfulness is the `toSheaf` route: `moduleRestriction ⋙ SheafOfModules.toSheaf` and
`SheafOfModules.toSheaf ⋙ v.sheafPushforwardContinuous AddCommGrpCat J K` are *equal*
(`moduleRestriction_comp_toSheaf`, proved by `rfl`), so faithfulness is inherited from
Mathlib's `IsCoverDense.faithful_sheafPushforwardContinuous`, and for fullness the
group-sheaf morphism produced by `IsCoverDense.full_sheafPushforwardContinuous` only has to
be shown `R`-linear. Linearity is local, so it is checked after restricting along the
`K`-cover of an object by the images of `v` (`Functor.IsCoverDense.ext`), where the morphism
*is* the given morphism of modules over the restricted ring.

Essential surjectivity is the only place that needs real work: a sheaf of abelian groups `G`
restricting to the underlying group sheaf of `N` has to be given an `R`-action over every
object of `C'`, not only over the images of `v`. The action is glued by Mathlib's own
Comparison Lemma machinery for presheaves of *types*: `scalarPairs R G` is the presheaf
`U ↦ R(U) × G(U)`, the action over the image of `v` is `imageAction`, and
`Functor.IsCoverDense.Types.presheafHom` extends it to `sectionAction`. Naturality of
`sectionAction` is exactly semilinearity of the restriction maps, and `appHom_restrict`
identifies the glued action over `v.obj Y` with the transported one, which reduces each
module axiom to the corresponding axiom in `N` after one application of
`Functor.IsCoverDense.ext`.

Every scalar and every section is handled through a `def` whose **result type is
ascribed** (`resG`, `resN`, `resRJ`, `toRJ`, `toN`, `fromN`, `mkPair`): the carrier of
`((ringRestriction J K v R).obj.obj X)` and that of `R.obj.obj (v.op.obj X)` are
definitionally equal but not syntactically so, because `sheafPushforwardContinuous` is a
semireducible `def`, and instance search for the `Module` structure, as well as `rw`'s motive
check, distinguish them. A type ascription on a term does not fix this — only a declared
result type does.

The single universe `w` for the sections of the ring sheaf and of the modules is forced by
`SheafOfModules`; the four universes of the two sites are free and independent.

## References

* [Stacks Project, Tag 03DG](https://stacks.math.columbia.edu/tag/03DG), method (2)
* [Stacks Project, Tag 00XU](https://stacks.math.columbia.edu/tag/00XU), the Comparison Lemma
-/

@[expose] public section

open CategoryTheory Functor Opposite

universe w u₁ v₁ u₂ v₂

namespace Stacks.DenseSubsiteModules


section Setup

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
  (J : GrothendieckTopology C) (K : GrothendieckTopology C')
  (v : C ⥤ C') [v.IsDenseSubsite J K]
  (R : Sheaf K RingCat.{w})

/-- The restriction of a sheaf of rings to a dense subsite. -/
abbrev ringRestriction : Sheaf J RingCat.{w} :=
  (v.sheafPushforwardContinuous RingCat.{w} J K).obj R

/-- The restriction of sheaves of modules to a dense subsite. -/
noncomputable abbrev moduleRestriction :
    SheafOfModules.{w} R ⥤ SheafOfModules.{w} (ringRestriction J K v R) :=
  SheafOfModules.pushforward (𝟙 (ringRestriction J K v R))

/-- Restricting a sheaf of modules and then taking its underlying sheaf of abelian groups is
the same as restricting the underlying sheaf of abelian groups. -/
lemma moduleRestriction_comp_toSheaf :
    moduleRestriction J K v R ⋙ SheafOfModules.toSheaf.{w} (ringRestriction J K v R) =
      SheafOfModules.toSheaf.{w} R ⋙ v.sheafPushforwardContinuous AddCommGrpCat.{w} J K := rfl

/-- Restriction of sheaves of modules to a dense subsite is faithful. -/
instance : (moduleRestriction J K v R).Faithful := by
  have := Functor.IsDenseSubsite.isCoverDense J K v
  have := Functor.IsDenseSubsite.isLocallyFull J K v
  have : (v.sheafPushforwardContinuous AddCommGrpCat.{w} J K).Faithful := inferInstance
  exact Functor.Faithful.of_comp_eq (moduleRestriction_comp_toSheaf J K v R)

/-- Restriction of sheaves of modules to a dense subsite is full. -/
instance : (moduleRestriction J K v R).Full where
  map_surjective {M N} f := by
    have := Functor.IsDenseSubsite.isCoverDense J K v
    have := Functor.IsDenseSubsite.isLocallyFull J K v
    have : (v.sheafPushforwardContinuous AddCommGrpCat.{w} J K).Full := inferInstance
    obtain ⟨g, hg⟩ := (v.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map_surjective
      (X := (SheafOfModules.toSheaf.{w} R).obj M) (Y := (SheafOfModules.toSheaf.{w} R).obj N)
      ((SheafOfModules.toSheaf.{w} (ringRestriction J K v R)).map f)
    have key : ∀ (Y : C) (x : M.val.obj (op (v.obj Y))),
        g.hom.app (op (v.obj Y)) x = f.val.app (op Y) x := by
      intro Y x
      have e := congrArg (fun p => (sheafToPresheaf J AddCommGrpCat.{w}).map p) hg
      exact CategoryTheory.congr_fun (NatTrans.congr_app e (op Y)) x
    refine ⟨⟨PresheafOfModules.homMk g.hom ?_⟩, ?_⟩
    · rintro ⟨X⟩ r m
      refine Functor.IsCoverDense.ext (K := K) v
        ((sheafCompose K (forget AddCommGrpCat.{w})).obj
          ((SheafOfModules.toSheaf.{w} R).obj N)) X (fun {Y} hY ↦ ?_)
      have nat : ∀ (x : M.val.obj (op X)),
          N.val.map hY.op (g.hom.app (op X) x) =
            g.hom.app (op (v.obj Y)) (M.val.map hY.op x) := fun x ↦
        (CategoryTheory.congr_fun (g.hom.naturality hY.op) x).symm
      refine (nat (r • m)).trans
        (Eq.trans ?_ (N.val.map_smul hY.op r (g.hom.app (op X) m)).symm)
      rw [M.val.map_smul]
      refine (key Y _).trans (((f.val.app (op Y)).hom.map_smul _ _).trans ?_)
      congr 1
      exact (key Y _).symm.trans (nat m).symm
    · exact SheafOfModules.Hom.ext <| PresheafOfModules.hom_ext fun Y ↦
        ModuleCat.hom_ext <| LinearMap.ext fun x ↦ key Y.unop x



end Setup

section EssSurj

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
  {J : GrothendieckTopology C} {K : GrothendieckTopology C'}
  {v : C ⥤ C'} [v.IsDenseSubsite J K] {R : Sheaf K RingCat.{w}}

/-- Pairs of a section of the sheaf of rings and a section of `G`, as a presheaf of types. -/
def scalarPairs (R : Sheaf K RingCat.{w}) (G : Sheaf K AddCommGrpCat.{w}) : C'ᵒᵖ ⥤ Type w where
  obj U := ↑(R.obj.obj U) × ↑(G.obj.obj U)
  map f := TypeCat.ofHom (fun p ↦ (R.obj.map f p.1, G.obj.map f p.2))
  map_id U := by
    ext p
    · exact CategoryTheory.congr_fun (R.obj.map_id U) p.1
    · exact CategoryTheory.congr_fun (G.obj.map_id U) p.2
  map_comp f g := by
    ext p
    · exact CategoryTheory.congr_fun (R.obj.map_comp f g) p.1
    · exact CategoryTheory.congr_fun (G.obj.map_comp f g) p.2

/-- The sheaf of types underlying a sheaf of abelian groups. -/
noncomputable abbrev typeSheaf (G : Sheaf K AddCommGrpCat.{w}) : Sheaf K (Type w) :=
  (sheafCompose K (forget AddCommGrpCat.{w})).obj G

/-- Restriction of sections of `G`, with the result type ascribed. -/
noncomputable def resG (G : Sheaf K AddCommGrpCat.{w}) {U U' : C'ᵒᵖ} (f : U ⟶ U')
    (x : ↑(G.obj.obj U)) : ↑(G.obj.obj U') := G.obj.map f x

section Transport

variable (N : SheafOfModules.{w} (ringRestriction J K v R)) (G : Sheaf K AddCommGrpCat.{w})
  (ι : (v.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj G ≅
    (SheafOfModules.toSheaf.{w} (ringRestriction J K v R)).obj N)

/-- Restriction of sections of `N`, with the result type ascribed. -/
noncomputable def resN (N : SheafOfModules.{w} (ringRestriction J K v R)) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (y : ↑(N.val.obj X)) : ↑(N.val.obj Y) := N.val.map f y

/-- Restriction of scalars of the restricted ring sheaf, with the result type ascribed.
`N` is an argument only to determine the topology `J`. -/
noncomputable def resRJ (_N : SheafOfModules.{w} (ringRestriction J K v R)) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (a : ↑((ringRestriction J K v R).obj.obj X)) : ↑((ringRestriction J K v R).obj.obj Y) :=
  (ringRestriction J K v R).obj.map f a

/-- A section of `R` over `v.obj X` read as a scalar for the restricted ring sheaf.
`N` is an argument only to determine the topology `J`. -/
def toRJ (_N : SheafOfModules.{w} (ringRestriction J K v R)) (X : Cᵒᵖ)
    (a : ↑(R.obj.obj (v.op.obj X))) : ↑((ringRestriction J K v R).obj.obj X) := a

/-- `ι` read as a map into the sections of `N`, with the result type ascribed. -/
noncomputable def toN (X : Cᵒᵖ) (x : ↑(G.obj.obj (v.op.obj X))) : ↑(N.val.obj X) :=
  ι.hom.hom.app X x

/-- The inverse of `toN`, with the result type ascribed. -/
noncomputable def fromN (X : Cᵒᵖ) (y : ↑(N.val.obj X)) : ↑(G.obj.obj (v.op.obj X)) :=
  ι.inv.hom.app X y

/-- The action of `R` on sections of `G` over an object in the image of `v`, transported
from `N` through `ι`. -/
noncomputable def imageSmul (X : Cᵒᵖ) (a : ↑(R.obj.obj (v.op.obj X)))
    (x : ↑(G.obj.obj (v.op.obj X))) : ↑(G.obj.obj (v.op.obj X)) :=
  fromN N G ι X (toRJ N X a • toN N G ι X x)

/-- `toRJ` sends `1` to `1`. -/
lemma toRJ_one (X : Cᵒᵖ) : toRJ N X 1 = 1 := rfl

/-- `toRJ` is multiplicative. -/
lemma toRJ_mul (X : Cᵒᵖ) (a b : ↑(R.obj.obj (v.op.obj X))) :
    toRJ N X (a * b) = toRJ N X a * toRJ N X b := rfl

/-- `toRJ` is additive. -/
lemma toRJ_add (X : Cᵒᵖ) (a b : ↑(R.obj.obj (v.op.obj X))) :
    toRJ N X (a + b) = toRJ N X a + toRJ N X b := rfl

/-- `toRJ` commutes with restriction of scalars along a morphism of `C`. -/
lemma toRJ_resRJ {X Y : Cᵒᵖ} (f : X ⟶ Y) (a : ↑(R.obj.obj (v.op.obj X))) :
    toRJ N Y (R.obj.map (v.op.map f) a) = resRJ N f (toRJ N X a) := rfl

/-- Restriction of sections of `N` is semilinear with respect to restriction of scalars. -/
lemma resN_smul {X Y : Cᵒᵖ} (f : X ⟶ Y) (a : ↑((ringRestriction J K v R).obj.obj X))
    (y : ↑(N.val.obj X)) : resN N f (a • y) = resRJ N f a • resN N f y :=
  N.val.map_smul f a y

/-- `imageSmul N G ι X a x` is `fromN` of `toRJ N X a • toN N G ι X x`. -/
lemma imageSmul_def (X : Cᵒᵖ) (a : ↑(R.obj.obj (v.op.obj X))) (x : ↑(G.obj.obj (v.op.obj X))) :
    imageSmul N G ι X a x = fromN N G ι X (toRJ N X a • toN N G ι X x) := rfl

/-- `toN` commutes with restriction of sections. -/
lemma toN_resN {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : ↑(G.obj.obj (v.op.obj X))) :
    resN N f (toN N G ι X x) = toN N G ι Y (resG G (v.op.map f) x) :=
  (CategoryTheory.congr_fun (ι.hom.hom.naturality f) x).symm

/-- `fromN` commutes with restriction of sections. -/
lemma fromN_resG {X Y : Cᵒᵖ} (f : X ⟶ Y) (y : ↑(N.val.obj X)) :
    resG G (v.op.map f) (fromN N G ι X y) = fromN N G ι Y (resN N f y) :=
  (CategoryTheory.congr_fun (ι.inv.hom.naturality f) y).symm

/-- `toN` is a left inverse of `fromN`. -/
lemma toN_fromN (X : Cᵒᵖ) (y : ↑(N.val.obj X)) : toN N G ι X (fromN N G ι X y) = y :=
  CategoryTheory.congr_fun (NatTrans.congr_app
    (congrArg (fun p ↦ (sheafToPresheaf J AddCommGrpCat.{w}).map p) ι.inv_hom_id) X) y

/-- `fromN` is a left inverse of `toN`. -/
lemma fromN_toN (X : Cᵒᵖ) (x : ↑(G.obj.obj (v.op.obj X))) :
    fromN N G ι X (toN N G ι X x) = x :=
  CategoryTheory.congr_fun (NatTrans.congr_app
    (congrArg (fun p ↦ (sheafToPresheaf J AddCommGrpCat.{w}).map p) ι.hom_inv_id) X) x

/-- `toN` is additive. -/
lemma toN_add (X : Cᵒᵖ) (x y : ↑(G.obj.obj (v.op.obj X))) :
    toN N G ι X (x + y) = toN N G ι X x + toN N G ι X y :=
  map_add (AddCommGrpCat.Hom.hom (ι.hom.hom.app X)) x y

/-- `fromN` is additive. -/
lemma fromN_add (X : Cᵒᵖ) (y z : ↑(N.val.obj X)) :
    fromN N G ι X (y + z) = fromN N G ι X y + fromN N G ι X z :=
  map_add (AddCommGrpCat.Hom.hom (ι.inv.hom.app X)) y z

/-- Restriction of sections of `G` along `v.op.map f` is semilinear for `imageSmul`. -/
lemma imageSmul_resG {X Y : Cᵒᵖ} (f : X ⟶ Y) (a : ↑(R.obj.obj (v.op.obj X)))
    (x : ↑(G.obj.obj (v.op.obj X))) :
    resG G (v.op.map f) (imageSmul N G ι X a x) =
      imageSmul N G ι Y (R.obj.map (v.op.map f) a) (resG G (v.op.map f) x) := by
  rw [imageSmul_def, fromN_resG, resN_smul, toN_resN, ← toRJ_resRJ, ← imageSmul_def]

/-- `1` acts trivially under `imageSmul`. -/
lemma imageSmul_one (X : Cᵒᵖ) (x : ↑(G.obj.obj (v.op.obj X))) : imageSmul N G ι X 1 x = x := by
  rw [imageSmul_def, toRJ_one, one_smul, fromN_toN]

/-- `imageSmul` is compatible with multiplication of scalars. -/
lemma imageSmul_mul (X : Cᵒᵖ) (a b : ↑(R.obj.obj (v.op.obj X))) (x : ↑(G.obj.obj (v.op.obj X))) :
    imageSmul N G ι X (a * b) x = imageSmul N G ι X a (imageSmul N G ι X b x) := by
  rw [imageSmul_def, imageSmul_def, imageSmul_def, toN_fromN, toRJ_mul, mul_smul]

/-- `imageSmul` is additive in the scalar. -/
lemma imageSmul_add_left (X : Cᵒᵖ) (a b : ↑(R.obj.obj (v.op.obj X)))
    (x : ↑(G.obj.obj (v.op.obj X))) :
    imageSmul N G ι X (a + b) x = imageSmul N G ι X a x + imageSmul N G ι X b x := by
  rw [imageSmul_def, imageSmul_def, imageSmul_def, toRJ_add, add_smul, fromN_add]

/-- `imageSmul` is additive in the section. -/
lemma imageSmul_add_right (X : Cᵒᵖ) (a : ↑(R.obj.obj (v.op.obj X)))
    (x y : ↑(G.obj.obj (v.op.obj X))) :
    imageSmul N G ι X a (x + y) = imageSmul N G ι X a x + imageSmul N G ι X a y := by
  rw [imageSmul_def, imageSmul_def, imageSmul_def, toN_add, smul_add, fromN_add]

/-- Restriction of sections of `G` is additive. -/
lemma resG_add (G : Sheaf K AddCommGrpCat.{w}) {U U' : C'ᵒᵖ} (f : U ⟶ U')
    (x y : ↑(G.obj.obj U)) : resG G f (x + y) = resG G f x + resG G f y :=
  map_add (AddCommGrpCat.Hom.hom (G.obj.map f)) x y

include N G ι in
/-- The transported action, as a morphism of presheaves of types on the subsite. -/
noncomputable def imageAction :
    v.op ⋙ scalarPairs R G ⟶ v.op ⋙ (typeSheaf G).obj where
  app X := TypeCat.ofHom (fun p ↦ imageSmul N G ι X p.1 p.2)
  naturality X Y f := by
    ext p
    exact (imageSmul_resG N G ι f p.1 p.2).symm

/-- Two sections of `G` over `U` agree if their restrictions along every morphism
`v.obj Y ⟶ U.unop` agree. -/
private lemma section_ext_op [v.IsCoverDense K] {U : C'ᵒᵖ} {s t : ↑(G.obj.obj U)}
    (h : ∀ (Y : C) (f : v.obj Y ⟶ U.unop), resG G f.op s = resG G f.op t) : s = t :=
  Functor.IsCoverDense.ext (K := K) v (typeSheaf G) U.unop (fun {Y} f ↦ h Y f)

section Gluing

variable [v.IsCoverDense K] [v.IsLocallyFull K]

include N G ι in
/-- The action of `R` on the sections of `G` over an arbitrary object, obtained from the
action over the image of `v` by the Comparison Lemma. -/
noncomputable def sectionAction : scalarPairs R G ⟶ (typeSheaf G).obj :=
  Functor.IsCoverDense.Types.presheafHom (imageAction N G ι)

/-- A pair of sections, with its type ascribed as a section of `scalarPairs`. -/
def mkPair (R : Sheaf K RingCat.{w}) (G : Sheaf K AddCommGrpCat.{w}) (U : C'ᵒᵖ)
    (a : ↑(R.obj.obj U)) (x : ↑(G.obj.obj U)) : (scalarPairs R G).obj U := Prod.mk a x

include N G ι in
/-- The glued scalar multiplication on the sections of `G`. -/
noncomputable def smulSection (U : C'ᵒᵖ) (a : ↑(R.obj.obj U)) (x : ↑(G.obj.obj U)) :
    ↑(G.obj.obj U) := TypeCat.homEquiv ((sectionAction N G ι).app U) (mkPair R G U a x)

/-- Restriction of sections of `G` is semilinear for `smulSection`. -/
lemma smulSection_resG {U U' : C'ᵒᵖ} (f : U ⟶ U') (a : ↑(R.obj.obj U)) (x : ↑(G.obj.obj U)) :
    resG G f (smulSection N G ι U a x) = smulSection N G ι U' (R.obj.map f a) (resG G f x) :=
  (CategoryTheory.congr_fun ((sectionAction N G ι).naturality f) (mkPair R G U a x)).symm

/-- Restricting `smulSection N G ι (op U) a x` along `h : v.obj Y ⟶ U` gives the transported
action `imageSmul` of the restrictions of `a` and `x`. -/
lemma smulSection_restrict {U : C'} {Y : C} (h : v.obj Y ⟶ U) (a : ↑(R.obj.obj (op U)))
    (x : ↑(G.obj.obj (op U))) :
    resG G h.op (smulSection N G ι (op U) a x) =
      imageSmul N G ι (op Y) (R.obj.map h.op a) (resG G h.op x) :=
  Functor.IsCoverDense.Types.appHom_restrict (imageAction N G ι) h.op
    (mkPair R G (op U) a x)

omit [v.IsLocallyFull K] in
/-- Two sections of `G` over `U` agree if their restrictions along every morphism
`v.obj Y ⟶ U` agree. -/
lemma section_ext {U : C'} {s t : ↑(G.obj.obj (op U))}
    (h : ∀ (Y : C) (f : v.obj Y ⟶ U), resG G f.op s = resG G f.op t) : s = t :=
  Functor.IsCoverDense.ext (K := K) v (typeSheaf G) U (fun {Y} f ↦ h Y f)

/-- `1` acts trivially under `smulSection`. -/
lemma smulSection_one (U : C'ᵒᵖ) (x : ↑(G.obj.obj U)) : smulSection N G ι U 1 x = x := by
  refine section_ext_op (v := v) G fun Y f ↦ ?_
  rw [smulSection_restrict, map_one, imageSmul_one]

/-- `smulSection` is compatible with multiplication of scalars. -/
lemma smulSection_mul (U : C'ᵒᵖ) (a b : ↑(R.obj.obj U)) (x : ↑(G.obj.obj U)) :
    smulSection N G ι U (a * b) x = smulSection N G ι U a (smulSection N G ι U b x) := by
  refine section_ext_op (v := v) G fun Y f ↦ ?_
  rw [smulSection_restrict, smulSection_restrict, smulSection_restrict, map_mul, imageSmul_mul]

/-- `smulSection` is additive in the scalar. -/
lemma smulSection_add_left (U : C'ᵒᵖ) (a b : ↑(R.obj.obj U)) (x : ↑(G.obj.obj U)) :
    smulSection N G ι U (a + b) x = smulSection N G ι U a x + smulSection N G ι U b x := by
  refine section_ext_op (v := v) G fun Y f ↦ ?_
  rw [resG_add, smulSection_restrict, smulSection_restrict, smulSection_restrict,
    _root_.map_add, imageSmul_add_left]

/-- `smulSection` is additive in the section. -/
lemma smulSection_add_right (U : C'ᵒᵖ) (a : ↑(R.obj.obj U)) (x y : ↑(G.obj.obj U)) :
    smulSection N G ι U a (x + y) = smulSection N G ι U a x + smulSection N G ι U a y := by
  refine section_ext_op (v := v) G fun Y f ↦ ?_
  rw [resG_add, smulSection_restrict, smulSection_restrict, smulSection_restrict, resG_add,
    imageSmul_add_right]

include N G ι in
/-- The `R`-module structure on the sections of `G` over `U`. -/
@[instance_reducible]
noncomputable def sectionModule (U : C'ᵒᵖ) : Module ↑(R.obj.obj U) ↑(G.obj.obj U) :=
  letI : SMul ↑(R.obj.obj U) ↑(G.obj.obj U) := ⟨smulSection N G ι U⟩
  Module.ofMinimalAxioms (smulSection_add_right N G ι U) (smulSection_add_left N G ι U)
    (smulSection_mul N G ι U) (smulSection_one N G ι U)

include N G ι in
/-- `G` as a presheaf of `R`-modules. -/
noncomputable def extPresheaf : PresheafOfModules.{w} R.obj :=
  letI := sectionModule N G ι
  PresheafOfModules.ofPresheaf G.obj (fun {_ _} f a x ↦ smulSection_resG N G ι f a x)

include N G ι in
/-- `G` as a sheaf of `R`-modules. -/
noncomputable def extSheaf : SheafOfModules.{w} R where
  val := extPresheaf N G ι
  isSheaf := G.property

/-- Over an object `v.obj Y`, `smulSection` is the transported action `imageSmul`. -/
lemma smulSection_image (Y : C) (a : ↑(R.obj.obj (op (v.obj Y))))
    (x : ↑(G.obj.obj (op (v.obj Y)))) :
    smulSection N G ι (op (v.obj Y)) a x = imageSmul N G ι (op Y) a x := by
  have h := smulSection_restrict N G ι (𝟙 (v.obj Y)) a x
  simpa [resG] using h

/-- `toN` carries `smulSection` over `v.obj Y` to scalar multiplication in `N`. -/
lemma toN_smulSection (Y : C) (r : ↑(R.obj.obj (op (v.obj Y)))) (x : ↑(G.obj.obj (op (v.obj Y)))) :
    toN N G ι (op Y) (smulSection N G ι (op (v.obj Y)) r x) =
      toRJ N (op Y) r • toN N G ι (op Y) x := by
  rw [smulSection_image, imageSmul_def, toN_fromN]

/-- `smulSection` over `v.obj Y` applied to `fromN m` is `fromN` of the scalar multiple of
`m` in `N`. -/
lemma smulSection_fromN (Y : C) (r : ↑(R.obj.obj (op (v.obj Y)))) (m : ↑(N.val.obj (op Y))) :
    smulSection N G ι (op (v.obj Y)) r (fromN N G ι (op Y) m) =
      fromN N G ι (op Y) (toRJ N (op Y) r • m) := by
  rw [smulSection_image, imageSmul_def, toN_fromN]

/-- The restriction of `extSheaf N G ι` to the subsite is `N`. -/
noncomputable def extIsoHom : (moduleRestriction J K v R).obj (extSheaf N G ι) ⟶ N :=
  ⟨PresheafOfModules.homMk ι.hom.hom (fun X r m ↦ by
    obtain ⟨Y⟩ := X
    exact toN_smulSection N G ι Y r m)⟩

/-- The inverse of `extIsoHom`. -/
noncomputable def extIsoInv : N ⟶ (moduleRestriction J K v R).obj (extSheaf N G ι) :=
  ⟨PresheafOfModules.homMk ι.inv.hom (fun X r m ↦ by
    obtain ⟨Y⟩ := X
    exact (smulSection_fromN N G ι Y r m).symm)⟩

/-- `N` is the restriction of a sheaf of `R`-modules. -/
noncomputable def extIso : (moduleRestriction J K v R).obj (extSheaf N G ι) ≅ N where
  hom := extIsoHom N G ι
  inv := extIsoInv N G ι
  hom_inv_id := SheafOfModules.Hom.ext <| PresheafOfModules.hom_ext fun X ↦
    ModuleCat.hom_ext <| LinearMap.ext fun x ↦ fromN_toN N G ι X x
  inv_hom_id := SheafOfModules.Hom.ext <| PresheafOfModules.hom_ext fun X ↦
    ModuleCat.hom_ext <| LinearMap.ext fun y ↦ toN_fromN N G ι X y

end Gluing

end Transport

/-- If the Comparison Lemma holds for sheaves of abelian groups, then restriction of sheaves
of modules to a dense subsite is essentially surjective. -/
instance essSurj_moduleRestriction
    [(v.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsEquivalence] :
    (moduleRestriction J K v R).EssSurj where
  mem_essImage N := by
    have := Functor.IsDenseSubsite.isCoverDense J K v
    have := Functor.IsDenseSubsite.isLocallyFull J K v
    exact ⟨extSheaf N _ ((v.sheafPushforwardContinuous AddCommGrpCat.{w} J K).objObjPreimageIso
      ((SheafOfModules.toSheaf.{w} (ringRestriction J K v R)).obj N)), ⟨extIso _ _ _⟩⟩

/-- If the Comparison Lemma holds for sheaves of abelian groups, then restriction of sheaves
of modules to a dense subsite is an equivalence. -/
instance isEquivalence_moduleRestriction
    [(v.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsEquivalence] :
    (moduleRestriction J K v R).IsEquivalence := Functor.IsEquivalence.mk

/-- **The Comparison Lemma for sheaves of modules.** If `v : C ⥤ C'` exhibits `(C, J)` as a
dense subsite of `(C', K)` and the Comparison Lemma holds for sheaves of abelian groups, then
restriction of sections along `v` is an equivalence from sheaves of `R`-modules to sheaves of
modules over the restricted ring sheaf. -/
noncomputable def moduleRestrictionEquivalence (J : GrothendieckTopology C)
    (K : GrothendieckTopology C') (v : C ⥤ C') [v.IsDenseSubsite J K] (R : Sheaf K RingCat.{w})
    [(v.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsEquivalence] :
    SheafOfModules.{w} R ≌ SheafOfModules.{w} (ringRestriction J K v R) :=
  (moduleRestriction J K v R).asEquivalence

end EssSurj

section Slice

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
  (J : GrothendieckTopology C) (K : GrothendieckTopology C')
  (v : C ⥤ C') [v.IsContinuous J K] (R : Sheaf K RingCat.{w}) (U : C)
  [(Over.post (X := U) v).IsContinuous (J.over U) (K.over (v.obj U))]

/-- **Restriction of a sheaf of rings along `v` commutes with restriction to a slice.** Both
sheaves on `Over U` send an object `W` to the sections of `R` over `v(W.left)`, because
`Over.post v ⋙ Over.forget (v U)` and `Over.forget U ⋙ v` are *equal* functors
(`CategoryTheory.Over.post_forget_eq_forget_comp`) and restriction of sections is precomposition
with the opposite functor; so the two are equal and not merely isomorphic. -/
theorem ringRestriction_over :
    ((v.sheafPushforwardContinuous RingCat.{w} J K).obj R).over U =
      ((Over.post (X := U) v).sheafPushforwardContinuous RingCat.{w}
        (J.over U) (K.over (v.obj U))).obj (R.over (v.obj U)) :=
  rfl

/-- **Restriction of sheaves of modules along `v` commutes with restriction to a slice.** Both
composites are `SheafOfModules.pushforward` along the one functor `Over.forget U ⋙ v` with the
identity structure map, by `ringRestriction_over`; so, again, they are equal and not merely
isomorphic. -/
theorem pushforward_comp_overFunctor :
    SheafOfModules.pushforward.{w} (F := v) (𝟙 _) ⋙
        SheafOfModules.overFunctor.{w} ((v.sheafPushforwardContinuous RingCat.{w} J K).obj R) U =
      SheafOfModules.overFunctor.{w} R (v.obj U) ⋙
        SheafOfModules.pushforward.{w} (F := Over.post (X := U) v) (𝟙 _) :=
  rfl

end Slice

section DenseSubsiteSlice

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
  (J : GrothendieckTopology C) (K : GrothendieckTopology C')
  (v : C ⥤ C') [v.IsDenseSubsite J K] (R : Sheaf K RingCat.{w}) (U : C)
  [(Over.post (X := U) v).IsDenseSubsite (J.over U) (K.over (v.obj U))]

/-- **Restriction of sheaves of modules to a dense subsite commutes with restriction to a
slice.** This is `pushforward_comp_overFunctor` read through the two restriction functors: the
slice `Over U ⥤ Over (v U)` of a dense subsite is again a dense subsite
(`Stacks.Sites.overPost_isDenseSubsite`), so both restrictions are `moduleRestriction`s, and the
two composites are equal.

With `moduleRestrictionEquivalence` this says that the Comparison Lemma for sheaves of modules
is compatible with localization: the equivalence `SheafOfModules R ≌ SheafOfModules (R|_C)` and
the corresponding equivalence of the slices commute with the two restrictions to the slices. -/
theorem moduleRestriction_comp_overFunctor :
    moduleRestriction J K v R ⋙ SheafOfModules.overFunctor.{w} (ringRestriction J K v R) U =
      SheafOfModules.overFunctor.{w} R (v.obj U) ⋙
        moduleRestriction (J.over U) (K.over (v.obj U)) (Over.post (X := U) v)
          (R.over (v.obj U)) :=
  rfl

end DenseSubsiteSlice

end Stacks.DenseSubsiteModules
