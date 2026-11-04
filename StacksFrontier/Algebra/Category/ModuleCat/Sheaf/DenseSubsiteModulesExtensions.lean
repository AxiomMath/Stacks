module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Module.MinimalAxioms
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import StacksCore.Tactic.StacksAttribute

/-!
# The Comparison Lemma for sheaves of modules, with an independent ring universe

Let `v : C ⥤ C'` exhibit `(C, J)` as a dense subsite of `(C', K)` and let `R` be a sheaf of rings
on `C'` whose sections live in a universe `r`. If restriction along `v` is an equivalence of
sheaves of abelian groups with sections in a universe `w`, then restriction along `v` is an
equivalence from sheaves of `R`-modules to sheaves of modules over the restricted ring sheaf.

## Main definitions

* `Stacks.DenseSubsiteModules.ringRestriction'`: The restriction of a sheaf of rings to a dense
  subsite.
* `Stacks.DenseSubsiteModules.moduleRestriction'`: The restriction of sheaves of modules to a
  dense subsite.
* `Stacks.DenseSubsiteModules.extSheaf'`: A sheaf of abelian groups on `C'` whose restriction is
  a sheaf of modules `N`, made into a sheaf of `R`-modules.
* `Stacks.DenseSubsiteModules.moduleRestrictionEquivalence'`: The equivalence from sheaves of
  `R`-modules to sheaves of modules over the restricted ring sheaf.

## Main results

* `Stacks.DenseSubsiteModules.essSurj_moduleRestriction'`: Restriction of sheaves of modules is
  essentially surjective.
* `Stacks.DenseSubsiteModules.isEquivalence_moduleRestriction'`: Restriction of sheaves of modules
  is an equivalence.
-/

@[expose] public section

open CategoryTheory Functor Opposite

universe w u₁ v₁ u₂ v₂

namespace Stacks.DenseSubsiteModules


/-! ### The Comparison Lemma for sheaves of modules, with an independent ring universe

The universe `r` of the sections of the ring sheaf is independent of the universe `w` of the
sections of the modules. Pairing a scalar with a section lands in
`Type (max r w)` (`Stacks.DenseSubsiteModules.scalarPairs'`), so the glued action maps into the
sheaf of sections of `G` raised to that universe, `Stacks.DenseSubsiteModules.typeSheaf'`, and
sections are read back through `Stacks.DenseSubsiteModules.upG'`. -/

universe r

section SetupOfUniv

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
  (J : GrothendieckTopology C) (K : GrothendieckTopology C')
  (v : C ⥤ C') [v.IsDenseSubsite J K]
  (R : Sheaf K RingCat.{r})

/-- The restriction of a sheaf of rings to a dense subsite. -/
abbrev ringRestriction' : Sheaf J RingCat.{r} :=
  (v.sheafPushforwardContinuous RingCat.{r} J K).obj R

/-- The restriction of sheaves of modules to a dense subsite. -/
noncomputable abbrev moduleRestriction' :
    SheafOfModules.{w} R ⥤ SheafOfModules.{w} (ringRestriction' J K v R) :=
  SheafOfModules.pushforward (𝟙 (ringRestriction' J K v R))

/-- Restricting a sheaf of modules and then forgetting to abelian groups is forgetting to abelian
groups and then restricting. -/
lemma moduleRestriction_comp_toSheaf' :
    moduleRestriction' J K v R ⋙ SheafOfModules.toSheaf.{w} (ringRestriction' J K v R) =
      SheafOfModules.toSheaf.{w} R ⋙ v.sheafPushforwardContinuous AddCommGrpCat.{w} J K := rfl

/-- Restriction of sheaves of modules to a dense subsite is faithful. -/
instance : (moduleRestriction' J K v R : SheafOfModules.{w} R ⥤ _).Faithful := by
  have := Functor.IsDenseSubsite.isCoverDense J K v
  have := Functor.IsDenseSubsite.isLocallyFull J K v
  have : (v.sheafPushforwardContinuous AddCommGrpCat.{w} J K).Faithful := inferInstance
  exact Functor.Faithful.of_comp_eq (moduleRestriction_comp_toSheaf' J K v R)

/-- Restriction of sheaves of modules to a dense subsite is full. -/
instance : (moduleRestriction' J K v R : SheafOfModules.{w} R ⥤ _).Full where
  map_surjective {M N} f := by
    have := Functor.IsDenseSubsite.isCoverDense J K v
    have := Functor.IsDenseSubsite.isLocallyFull J K v
    have : (v.sheafPushforwardContinuous AddCommGrpCat.{w} J K).Full := inferInstance
    obtain ⟨g, hg⟩ := (v.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map_surjective
      (X := (SheafOfModules.toSheaf.{w} R).obj M) (Y := (SheafOfModules.toSheaf.{w} R).obj N)
      ((SheafOfModules.toSheaf.{w} (ringRestriction' J K v R)).map f)
    have key : ∀ (Y : C) (x : M.val.obj (op (v.obj Y))),
        g.hom.app (op (v.obj Y)) x = f.val.app (op Y) x := fun Y x ↦
      CategoryTheory.congr_fun (NatTrans.congr_app
        (congrArg (fun p => (sheafToPresheaf J AddCommGrpCat.{w}).map p) hg) (op Y)) x
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

end SetupOfUniv

section EssSurjOfUniv

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
  {J : GrothendieckTopology C} {K : GrothendieckTopology C'}
  {v : C ⥤ C'} [v.IsDenseSubsite J K] {R : Sheaf K RingCat.{r}}

/-- Pairs of a section of the sheaf of rings and a section of `G`, as a presheaf of types. -/
def scalarPairs' (R : Sheaf K RingCat.{r}) (G : Sheaf K AddCommGrpCat.{w}) :
    C'ᵒᵖ ⥤ Type (max r w) where
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

/-- The sheaf of types underlying a sheaf of abelian groups, raised to the universe in which a
scalar pairs with a section.  The ring sheaf is an argument only to determine the universe `r`
of the scalars. -/
noncomputable abbrev typeSheaf' (_R : Sheaf K RingCat.{r}) (G : Sheaf K AddCommGrpCat.{w}) :
    Sheaf K (Type (max r w)) :=
  (sheafCompose K uliftFunctor.{r, w}).obj
    ((sheafCompose K (forget AddCommGrpCat.{w})).obj G)

/-- A section of `G`, read as a section of `Stacks.DenseSubsiteModules.typeSheaf'`. -/
def upG' (R : Sheaf K RingCat.{r}) (G : Sheaf K AddCommGrpCat.{w}) (U : C'ᵒᵖ)
    (x : ↑(G.obj.obj U)) : (typeSheaf' R G).obj.obj U := ULift.up x

/-- `Stacks.DenseSubsiteModules.upG'` is injective. -/
lemma upG_injective' (R : Sheaf K RingCat.{r}) (G : Sheaf K AddCommGrpCat.{w}) (U : C'ᵒᵖ)
    {x y : ↑(G.obj.obj U)} (h : upG' R G U x = upG' R G U y) : x = y :=
  congrArg ULift.down h

section Transport

variable (N : SheafOfModules.{w} (ringRestriction' J K v R)) (G : Sheaf K AddCommGrpCat.{w})
  (ι : (v.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj G ≅
    (SheafOfModules.toSheaf.{w} (ringRestriction' J K v R)).obj N)

/-- Restriction of sections of `N`, with the result type ascribed. -/
noncomputable def resN' (N : SheafOfModules.{w} (ringRestriction' J K v R)) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (y : ↑(N.val.obj X)) : ↑(N.val.obj Y) := N.val.map f y

/-- Restriction of scalars of the restricted ring sheaf, with the result type ascribed.
`N` is an argument only to determine the topology `J`. -/
noncomputable def resRJ' (_N : SheafOfModules.{w} (ringRestriction' J K v R)) {X Y : Cᵒᵖ}
    (f : X ⟶ Y) (a : ↑((ringRestriction' J K v R).obj.obj X)) :
    ↑((ringRestriction' J K v R).obj.obj Y) :=
  (ringRestriction' J K v R).obj.map f a

/-- A section of `R` over `v.obj X` read as a scalar for the restricted ring sheaf.
`N` is an argument only to determine the topology `J`. -/
def toRJ' (_N : SheafOfModules.{w} (ringRestriction' J K v R)) (X : Cᵒᵖ)
    (a : ↑(R.obj.obj (v.op.obj X))) : ↑((ringRestriction' J K v R).obj.obj X) := a

/-- `ι` read as a map into the sections of `N`, with the result type ascribed. -/
noncomputable def toN'
    {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
    {J : GrothendieckTopology C} {K : GrothendieckTopology C'}
    {v : C ⥤ C'} [v.IsDenseSubsite J K] {R : Sheaf K RingCat.{r}}
    (N : SheafOfModules.{w} (ringRestriction' J K v R)) (G : Sheaf K AddCommGrpCat.{w})
    (ι : (v.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj G ≅
    (SheafOfModules.toSheaf.{w} (ringRestriction' J K v R)).obj N)
    (X : Cᵒᵖ) (x : ↑(G.obj.obj (v.op.obj X))) : ↑(N.val.obj X) :=
  ι.hom.hom.app X x

/-- The inverse of `toN'`, with the result type ascribed. -/
noncomputable def fromN'
    {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
    {J : GrothendieckTopology C} {K : GrothendieckTopology C'}
    {v : C ⥤ C'} [v.IsDenseSubsite J K] {R : Sheaf K RingCat.{r}}
    (N : SheafOfModules.{w} (ringRestriction' J K v R)) (G : Sheaf K AddCommGrpCat.{w})
    (ι : (v.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj G ≅
    (SheafOfModules.toSheaf.{w} (ringRestriction' J K v R)).obj N)
    (X : Cᵒᵖ) (y : ↑(N.val.obj X)) : ↑(G.obj.obj (v.op.obj X)) :=
  ι.inv.hom.app X y

/-- The action of `R` on sections of `G` over an object in the image of `v`, transported
from `N` through `ι`. -/
noncomputable def imageSmul' (X : Cᵒᵖ) (a : ↑(R.obj.obj (v.op.obj X)))
    (x : ↑(G.obj.obj (v.op.obj X))) : ↑(G.obj.obj (v.op.obj X)) :=
  fromN' N G ι X (toRJ' N X a • toN' N G ι X x)

/-- `toRJ'` sends `1` to `1`. -/
lemma toRJ_one' (X : Cᵒᵖ) : toRJ' N X 1 = 1 := rfl

/-- `toRJ'` is multiplicative. -/
lemma toRJ_mul' (X : Cᵒᵖ) (a b : ↑(R.obj.obj (v.op.obj X))) :
    toRJ' N X (a * b) = toRJ' N X a * toRJ' N X b := rfl

/-- `toRJ'` is additive. -/
lemma toRJ_add' (X : Cᵒᵖ) (a b : ↑(R.obj.obj (v.op.obj X))) :
    toRJ' N X (a + b) = toRJ' N X a + toRJ' N X b := rfl

/-- `toRJ'` commutes with restriction of sections of the ring sheaf. -/
lemma toRJ_resRJ' {X Y : Cᵒᵖ} (f : X ⟶ Y) (a : ↑(R.obj.obj (v.op.obj X))) :
    toRJ' N Y (R.obj.map (v.op.map f) a) = resRJ' N f (toRJ' N X a) := rfl

/-- Restriction of sections of `N` is semilinear along restriction of sections of the ring
sheaf. -/
lemma resN_smul' {X Y : Cᵒᵖ} (f : X ⟶ Y) (a : ↑((ringRestriction' J K v R).obj.obj X))
    (y : ↑(N.val.obj X)) : resN' N f (a • y) = resRJ' N f a • resN' N f y :=
  N.val.map_smul f a y

/-- The defining formula of `imageSmul'`. -/
lemma imageSmul_def' (X : Cᵒᵖ) (a : ↑(R.obj.obj (v.op.obj X))) (x : ↑(G.obj.obj (v.op.obj X))) :
    imageSmul' N G ι X a x = fromN' N G ι X (toRJ' N X a • toN' N G ι X x) := rfl

/-- `toN'` commutes with restriction. -/
lemma toN_resN' {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : ↑(G.obj.obj (v.op.obj X))) :
    resN' N f (toN' N G ι X x) = toN' N G ι Y (resG G (v.op.map f) x) :=
  (CategoryTheory.congr_fun (ι.hom.hom.naturality f) x).symm

/-- `fromN'` commutes with restriction. -/
lemma fromN_resG' {X Y : Cᵒᵖ} (f : X ⟶ Y) (y : ↑(N.val.obj X)) :
    resG G (v.op.map f) (fromN' N G ι X y) = fromN' N G ι Y (resN' N f y) :=
  (CategoryTheory.congr_fun (ι.inv.hom.naturality f) y).symm

/-- `toN'` is a left inverse of `fromN'`. -/
lemma toN_fromN' (X : Cᵒᵖ) (y : ↑(N.val.obj X)) : toN' N G ι X (fromN' N G ι X y) = y :=
  congrArg (fun p ↦ p.hom.app X y) ι.inv_hom_id

/-- `fromN'` is a left inverse of `toN'`. -/
lemma fromN_toN' (X : Cᵒᵖ) (x : ↑(G.obj.obj (v.op.obj X))) :
    fromN' N G ι X (toN' N G ι X x) = x :=
  congrArg (fun p ↦ p.hom.app X x) ι.hom_inv_id

/-- `toN'` is additive. -/
lemma toN_add' (X : Cᵒᵖ) (x y : ↑(G.obj.obj (v.op.obj X))) :
    toN' N G ι X (x + y) = toN' N G ι X x + toN' N G ι X y :=
  map_add (AddCommGrpCat.Hom.hom (ι.hom.hom.app X)) x y

/-- `fromN'` is additive. -/
lemma fromN_add' (X : Cᵒᵖ) (y z : ↑(N.val.obj X)) :
    fromN' N G ι X (y + z) = fromN' N G ι X y + fromN' N G ι X z :=
  map_add (AddCommGrpCat.Hom.hom (ι.inv.hom.app X)) y z

/-- `imageSmul'` commutes with restriction along morphisms of the subsite. -/
lemma imageSmul_resG' {X Y : Cᵒᵖ} (f : X ⟶ Y) (a : ↑(R.obj.obj (v.op.obj X)))
    (x : ↑(G.obj.obj (v.op.obj X))) :
    resG G (v.op.map f) (imageSmul' N G ι X a x) =
      imageSmul' N G ι Y (R.obj.map (v.op.map f) a) (resG G (v.op.map f) x) := by
  rw [imageSmul_def', fromN_resG', resN_smul', toN_resN', ← toRJ_resRJ', ← imageSmul_def']

/-- The scalar `1` acts trivially under `imageSmul'`. -/
lemma imageSmul_one' (X : Cᵒᵖ) (x : ↑(G.obj.obj (v.op.obj X))) : imageSmul' N G ι X 1 x = x := by
  rw [imageSmul_def', toRJ_one', one_smul, fromN_toN']

/-- `imageSmul'` by a product is the composite of the actions of the factors. -/
lemma imageSmul_mul' (X : Cᵒᵖ) (a b : ↑(R.obj.obj (v.op.obj X))) (x : ↑(G.obj.obj (v.op.obj X))) :
    imageSmul' N G ι X (a * b) x = imageSmul' N G ι X a (imageSmul' N G ι X b x) := by
  rw [imageSmul_def', imageSmul_def', imageSmul_def', toN_fromN', toRJ_mul', mul_smul]

/-- `imageSmul'` is additive in the scalar. -/
lemma imageSmul_add_left' (X : Cᵒᵖ) (a b : ↑(R.obj.obj (v.op.obj X)))
    (x : ↑(G.obj.obj (v.op.obj X))) :
    imageSmul' N G ι X (a + b) x = imageSmul' N G ι X a x + imageSmul' N G ι X b x := by
  rw [imageSmul_def', imageSmul_def', imageSmul_def', toRJ_add', add_smul, fromN_add']

/-- `imageSmul'` is additive in the section. -/
lemma imageSmul_add_right' (X : Cᵒᵖ) (a : ↑(R.obj.obj (v.op.obj X)))
    (x y : ↑(G.obj.obj (v.op.obj X))) :
    imageSmul' N G ι X a (x + y) = imageSmul' N G ι X a x + imageSmul' N G ι X a y := by
  rw [imageSmul_def', imageSmul_def', imageSmul_def', toN_add', smul_add, fromN_add']

include N G ι in
/-- The transported action, as a morphism of presheaves of types on the subsite. -/
noncomputable def imageAction' :
    v.op ⋙ scalarPairs' R G ⟶ v.op ⋙ (typeSheaf' R G).obj where
  app X := TypeCat.ofHom (fun p ↦ upG' R G (v.op.obj X) (imageSmul' N G ι X p.1 p.2))
  naturality X Y f := by
    ext p
    exact congrArg (upG' R G (v.op.obj Y)) (imageSmul_resG' N G ι f p.1 p.2).symm

section Gluing

variable [v.IsCoverDense K] [v.IsLocallyFull K]

include N G ι in
/-- The action of `R` on the sections of `G` over an arbitrary object, obtained from the
action over the image of `v` by the Comparison Lemma. -/
noncomputable def sectionAction' : scalarPairs' R G ⟶ (typeSheaf' R G).obj :=
  Functor.IsCoverDense.Types.presheafHom (imageAction' N G ι)

/-- A pair of sections, with its type ascribed as a section of `scalarPairs'`. -/
def mkPair' (R : Sheaf K RingCat.{r}) (G : Sheaf K AddCommGrpCat.{w}) (U : C'ᵒᵖ)
    (a : ↑(R.obj.obj U)) (x : ↑(G.obj.obj U)) : (scalarPairs' R G).obj U := Prod.mk a x

include N G ι in
/-- The glued scalar multiplication on the sections of `G`. -/
noncomputable def smulSection' (U : C'ᵒᵖ) (a : ↑(R.obj.obj U)) (x : ↑(G.obj.obj U)) :
    ↑(G.obj.obj U) :=
  (TypeCat.homEquiv ((sectionAction' N G ι).app U) (mkPair' R G U a x)).down

/-- `smulSection'`, read in `Stacks.DenseSubsiteModules.typeSheaf'`, is the value of
`sectionAction'`. -/
lemma upG_smulSection' (U : C'ᵒᵖ) (a : ↑(R.obj.obj U)) (x : ↑(G.obj.obj U)) :
    upG' R G U (smulSection' N G ι U a x) =
      TypeCat.homEquiv ((sectionAction' N G ι).app U) (mkPair' R G U a x) := rfl

/-- `smulSection'` commutes with restriction. -/
lemma smulSection_resG' {U U' : C'ᵒᵖ} (f : U ⟶ U') (a : ↑(R.obj.obj U)) (x : ↑(G.obj.obj U)) :
    resG G f (smulSection' N G ι U a x) = smulSection' N G ι U' (R.obj.map f a) (resG G f x) :=
  upG_injective' R G U'
    ((CategoryTheory.congr_fun ((sectionAction' N G ι).naturality f)
      (mkPair' R G U a x)).symm)

/-- Restricting `smulSection'` to an object `v.obj Y` gives `imageSmul'` of the restrictions. -/
lemma smulSection_restrict' {U : C'} {Y : C} (h : v.obj Y ⟶ U) (a : ↑(R.obj.obj (op U)))
    (x : ↑(G.obj.obj (op U))) :
    resG G h.op (smulSection' N G ι (op U) a x) =
      imageSmul' N G ι (op Y) (R.obj.map h.op a) (resG G h.op x) :=
  upG_injective' R G (op (v.obj Y))
    (Functor.IsCoverDense.Types.appHom_restrict (imageAction' N G ι) h.op
      (mkPair' R G (op U) a x))

omit [v.IsLocallyFull K] in
/-- Two sections of `G` over the same object agree as soon as they agree after restriction to
every object of the subsite over it.  The ring sheaf is an argument only to determine the
universe of the scalars. -/
lemma section_ext' (R : Sheaf K RingCat.{r}) {U : C'} {s t : ↑(G.obj.obj (op U))}
    (h : ∀ (Y : C) (f : v.obj Y ⟶ U), resG G f.op s = resG G f.op t) : s = t :=
  upG_injective' R G (op U)
    (Functor.IsCoverDense.ext (K := K) v (typeSheaf' R G) U
      (fun {Y} f ↦ congrArg (upG' R G (op (v.obj Y))) (h Y f)))

/-- The scalar `1` acts trivially under `smulSection'`. -/
lemma smulSection_one' (U : C'ᵒᵖ) (x : ↑(G.obj.obj U)) : smulSection' N G ι U 1 x = x := by
  obtain ⟨U⟩ := U
  refine section_ext' (v := v) G R (fun Y f ↦ ?_)
  rw [smulSection_restrict', map_one, imageSmul_one']

/-- `smulSection'` by a product is the composite of the actions of the factors. -/
lemma smulSection_mul' (U : C'ᵒᵖ) (a b : ↑(R.obj.obj U)) (x : ↑(G.obj.obj U)) :
    smulSection' N G ι U (a * b) x = smulSection' N G ι U a (smulSection' N G ι U b x) := by
  obtain ⟨U⟩ := U
  refine section_ext' (v := v) G R (fun Y f ↦ ?_)
  rw [smulSection_restrict', smulSection_restrict', smulSection_restrict', map_mul, imageSmul_mul']

/-- `smulSection'` is additive in the scalar. -/
lemma smulSection_add_left' (U : C'ᵒᵖ) (a b : ↑(R.obj.obj U)) (x : ↑(G.obj.obj U)) :
    smulSection' N G ι U (a + b) x = smulSection' N G ι U a x + smulSection' N G ι U b x := by
  obtain ⟨U⟩ := U
  refine section_ext' (v := v) G R (fun Y f ↦ ?_)
  rw [resG_add, smulSection_restrict', smulSection_restrict', smulSection_restrict',
    _root_.map_add, imageSmul_add_left']

/-- `smulSection'` is additive in the section. -/
lemma smulSection_add_right' (U : C'ᵒᵖ) (a : ↑(R.obj.obj U)) (x y : ↑(G.obj.obj U)) :
    smulSection' N G ι U a (x + y) = smulSection' N G ι U a x + smulSection' N G ι U a y := by
  obtain ⟨U⟩ := U
  refine section_ext' (v := v) G R (fun Y f ↦ ?_)
  rw [resG_add, smulSection_restrict', smulSection_restrict', smulSection_restrict', resG_add,
    imageSmul_add_right']

include N G ι in
/-- The `R`-module structure on the sections of `G` over `U`. -/
@[instance_reducible]
noncomputable def sectionModule' (U : C'ᵒᵖ) : Module ↑(R.obj.obj U) ↑(G.obj.obj U) :=
  letI : SMul ↑(R.obj.obj U) ↑(G.obj.obj U) := ⟨smulSection' N G ι U⟩
  Module.ofMinimalAxioms (smulSection_add_right' N G ι U) (smulSection_add_left' N G ι U)
    (smulSection_mul' N G ι U) (smulSection_one' N G ι U)

include N G ι in
/-- `G` as a presheaf of `R`-modules. -/
noncomputable def extPresheaf' : PresheafOfModules.{w} R.obj :=
  letI := sectionModule' N G ι
  PresheafOfModules.ofPresheaf G.obj (fun {_ _} f a x ↦ smulSection_resG' N G ι f a x)

include N G ι in
/-- `G` as a sheaf of `R`-modules. -/
noncomputable def extSheaf' : SheafOfModules.{w} R where
  val := extPresheaf' N G ι
  isSheaf := G.property

/-- Over an object `v.obj Y`, `smulSection'` is `imageSmul'`. -/
lemma smulSection_image' (Y : C) (a : ↑(R.obj.obj (op (v.obj Y))))
    (x : ↑(G.obj.obj (op (v.obj Y)))) :
    smulSection' N G ι (op (v.obj Y)) a x = imageSmul' N G ι (op Y) a x := by
  simpa [resG] using smulSection_restrict' N G ι (𝟙 (v.obj Y)) a x

/-- `toN'` carries `smulSection'` to the scalar action on `N`. -/
lemma toN_smulSection' (Y : C) (r : ↑(R.obj.obj (op (v.obj Y)))) (x : ↑(G.obj.obj (op (v.obj Y)))) :
    toN' N G ι (op Y) (smulSection' N G ι (op (v.obj Y)) r x) =
      toRJ' N (op Y) r • toN' N G ι (op Y) x := by
  rw [smulSection_image', imageSmul_def', toN_fromN']

/-- `fromN'` carries the scalar action on `N` to `smulSection'`. -/
lemma smulSection_fromN' (Y : C) (r : ↑(R.obj.obj (op (v.obj Y)))) (m : ↑(N.val.obj (op Y))) :
    smulSection' N G ι (op (v.obj Y)) r (fromN' N G ι (op Y) m) =
      fromN' N G ι (op Y) (toRJ' N (op Y) r • m) := by
  rw [smulSection_image', imageSmul_def', toN_fromN']

/-- The restriction of `extSheaf' N G ι` to the subsite is `N`. -/
noncomputable def extIsoHom' : (moduleRestriction' J K v R).obj (extSheaf' N G ι) ⟶ N :=
  ⟨PresheafOfModules.homMk ι.hom.hom (fun X r m ↦ by
    obtain ⟨Y⟩ := X
    exact toN_smulSection' N G ι Y r m)⟩

/-- The inverse of `extIsoHom'`. -/
noncomputable def extIsoInv' : N ⟶ (moduleRestriction' J K v R).obj (extSheaf' N G ι) :=
  ⟨PresheafOfModules.homMk ι.inv.hom (fun X r m ↦ by
    obtain ⟨Y⟩ := X
    exact (smulSection_fromN' N G ι Y r m).symm)⟩

/-- `N` is the restriction of a sheaf of `R`-modules. -/
noncomputable def extIso' : (moduleRestriction' J K v R).obj (extSheaf' N G ι) ≅ N where
  hom := extIsoHom' N G ι
  inv := extIsoInv' N G ι
  hom_inv_id := SheafOfModules.Hom.ext <| PresheafOfModules.hom_ext fun X ↦
    ModuleCat.hom_ext <| LinearMap.ext fun x ↦ fromN_toN' N G ι X x
  inv_hom_id := SheafOfModules.Hom.ext <| PresheafOfModules.hom_ext fun X ↦
    ModuleCat.hom_ext <| LinearMap.ext fun y ↦ toN_fromN' N G ι X y

end Gluing

end Transport

/-- If restriction of sheaves of abelian groups to a dense subsite is an equivalence, then
restriction of sheaves of modules is essentially surjective. -/
instance essSurj_moduleRestriction'
    [(v.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsEquivalence] :
    (moduleRestriction' J K v R : SheafOfModules.{w} R ⥤ _).EssSurj where
  mem_essImage N := by
    have := Functor.IsDenseSubsite.isCoverDense J K v
    have := Functor.IsDenseSubsite.isLocallyFull J K v
    exact ⟨extSheaf' N _ ((v.sheafPushforwardContinuous AddCommGrpCat.{w} J K).objObjPreimageIso
      ((SheafOfModules.toSheaf.{w} (ringRestriction' J K v R)).obj N)), ⟨extIso' _ _ _⟩⟩

/-- If restriction of sheaves of abelian groups to a dense subsite is an equivalence, then so is
restriction of sheaves of modules. -/
instance isEquivalence_moduleRestriction'
    [(v.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsEquivalence] :
    (moduleRestriction' J K v R : SheafOfModules.{w} R ⥤ _).IsEquivalence :=
  Functor.IsEquivalence.mk

/-- **The Comparison Lemma for sheaves of modules.** If `v : C ⥤ C'` exhibits `(C, J)` as a
dense subsite of `(C', K)` and the Comparison Lemma holds for sheaves of abelian groups, then
restriction of sections along `v` is an equivalence from sheaves of `R`-modules to sheaves of
modules over the restricted ring sheaf. -/
noncomputable def moduleRestrictionEquivalence' (J : GrothendieckTopology C)
    (K : GrothendieckTopology C') (v : C ⥤ C') [v.IsDenseSubsite J K] (R : Sheaf K RingCat.{r})
    [(v.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsEquivalence] :
    SheafOfModules.{w} R ≌ SheafOfModules.{w} (ringRestriction' J K v R) :=
  (moduleRestriction' J K v R).asEquivalence

end EssSurjOfUniv

section Setup

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
  (J : GrothendieckTopology C) (K : GrothendieckTopology C')
  (v : C ⥤ C') [v.IsDenseSubsite J K]
  (R : Sheaf K RingCat.{w})

end Setup

section EssSurj

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
  {J : GrothendieckTopology C} {K : GrothendieckTopology C'}
  {v : C ⥤ C'} [v.IsDenseSubsite J K] {R : Sheaf K RingCat.{w}}

section Transport

variable (N : SheafOfModules.{w} (ringRestriction J K v R)) (G : Sheaf K AddCommGrpCat.{w})
  (ι : (v.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj G ≅
    (SheafOfModules.toSheaf.{w} (ringRestriction J K v R)).obj N)

section Gluing

variable [v.IsCoverDense K] [v.IsLocallyFull K]

end Gluing

end Transport

end EssSurj

section Slice

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
  (J : GrothendieckTopology C) (K : GrothendieckTopology C')
  (v : C ⥤ C') [v.IsContinuous J K] (R : Sheaf K RingCat.{w}) (U : C)
  [(Over.post (X := U) v).IsContinuous (J.over U) (K.over (v.obj U))]

end Slice

section DenseSubsiteSlice

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
  (J : GrothendieckTopology C) (K : GrothendieckTopology C')
  (v : C ⥤ C') [v.IsDenseSubsite J K] (R : Sheaf K RingCat.{w}) (U : C)
  [(Over.post (X := U) v).IsDenseSubsite (J.over U) (K.over (v.obj U))]

end DenseSubsiteSlice

end Stacks.DenseSubsiteModules
