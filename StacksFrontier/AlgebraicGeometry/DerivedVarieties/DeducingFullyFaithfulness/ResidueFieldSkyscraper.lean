module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Skyscraper
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.AlgebraicGeometry.Modules.SpecFieldDerivedPullback
public import StacksFrontier.AlgebraicGeometry.LocalIso.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.FiniteType
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.FlatModuleSheavesAndStalks
public import StacksFrontier.Topology.Sheaves.Skyscraper.Adjunction
public import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology at a point and maps to its skyscraper sheaf

Let `X` be a Noetherian scheme and `x` a point of it. For a bounded complex of
`𝒪_X`-modules with coherent cohomology, the stalks at `x` of its cohomology sheaves vanish above a
degree `b` exactly when every map into the residue-field skyscraper at `x`, placed in a degree
above `b`, vanishes. The proof identifies the two sides through the adjunction between the stalk
functor at `x` and the skyscraper functor at `x`, which is exact on both sides and therefore
induces an adjunction of derived categories.

Taking `b` arbitrary, such a complex orthogonal to every shift of the skyscraper has all of its
cohomology stalks at `x` zero, and then — the cohomology sheaves being coherent and only finitely
many of them nonzero — it is zero on a whole open neighbourhood of `x`.

## Main definitions

* `AlgebraicGeometry.residueFieldSkyscraper`: the sheaf of modules supported at a point and
  carrying its residue field.

## Main results

* `AlgebraicGeometry.stalkHomology_isZero_iff_hom_residueFieldSkyscraper_subsingleton`: the
  vanishing criterion.
* `AlgebraicGeometry.exists_mem_forall_stalkHomology_isZero_of_hom_residueFieldSkyscraper`:
  total orthogonality to the skyscraper forces vanishing near the point.

## Implementation notes

The bounded coherent derived category is represented by bounded objects of the derived category of
all modules whose cohomology sheaves are coherent. The skyscraper is built by sheafifying the
existing skyscraper presheaf of modules; since that presheaf is already a sheaf, the two
constructions are identified by `skyscraperSheafificationIso`. The shift of the skyscraper by `-i`
is represented by the single-object functor in degree `i`, and vanishing of a Hom group by
`Subsingleton`.

## References

* [Stacks Project, Tag 0GWZ](https://stacks.math.columbia.edu/tag/0GWZ)
* [Stacks Project, Tag 0G03](https://stacks.math.columbia.edu/tag/0G03)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Triangulated TopologicalSpace TensorProduct Opposite

universe u

namespace AlgebraicGeometry

/-- The skyscraper sheaf of `𝒪_X`-modules at `x` with fibre `κ(x)`. -/
public noncomputable def residueFieldSkyscraper (X : Scheme.{u}) (x : X) : X.Modules := by
  letI : Algebra (X.presheaf.stalk x) (X.residueField x) :=
    (X.residue x).hom.toAlgebra
  exact OXModule.sheafify.obj
    (OXModule.skyscraperPOM x (ModuleCat.of _ (X.residueField x)))

-- The skyscraper presheaf is defined by a case distinction on whether the point lies in the
-- open set, so the constructions below need that membership to be decidable.
attribute [local instance] Classical.propDecidable

/-- The stalk at `x` of a sheaf of `𝒪_X`-modules, as a functor to modules over the local ring
at `x`. -/
private noncomputable def stalkAt (X : Scheme.{u}) (x : X) :
    OXModule X.toRingedSpace ⥤ ModuleCat.{u} (X.toRingedSpace.presheaf.stalk x) where
  obj M := OXModule.stalk (X := X.toRingedSpace) M x
  map {M N} f :=
    ConcreteCategory.ofHom (OXModule.stalkLinearMap (X := X.toRingedSpace) M N f x)
  map_id M := by
    apply ModuleCat.hom_ext
    ext z
    change (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor _ x).map
      ((PresheafOfModules.toPresheaf _).map (𝟙 M.val)))) z = z
    have h : (TopCat.Presheaf.stalkFunctor _ x).map
        ((PresheafOfModules.toPresheaf _).map (𝟙 M.val)) = 𝟙 _ := by
      simp
    simp
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    ext z
    change (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor _ x).map
      ((PresheafOfModules.toPresheaf _).map (f.val ≫ g.val)))) z =
      (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor _ x).map
        ((PresheafOfModules.toPresheaf _).map g.val)))
        ((ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor _ x).map
          ((PresheafOfModules.toPresheaf _).map f.val))) z)
    have h : (TopCat.Presheaf.stalkFunctor _ x).map
        ((PresheafOfModules.toPresheaf _).map (f.val ≫ g.val)) =
      (TopCat.Presheaf.stalkFunctor _ x).map
        ((PresheafOfModules.toPresheaf _).map f.val ≫
          (PresheafOfModules.toPresheaf _).map g.val) := by
      simp
    simp [Functor.map_comp]
    rfl

/-- The underlying presheaf of abelian groups of the skyscraper presheaf of modules at `x` is the
skyscraper presheaf of the underlying group. -/
private noncomputable def skyscraperPOM_underlyingIso (X : Scheme.{u}) (x : X)
    [∀ U : Opens X.carrier, Decidable (x ∈ U)]
    (N : ModuleCat.{u} (X.presheaf.stalk x)) :
    (OXModule.skyscraperPOM x N).presheaf ≅
      skyscraperPresheaf x
        ((forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).obj N) := by
  classical
  refine NatIso.ofComponents (fun U => ?_) ?_
  · by_cases hx : x ∈ U.unop
    · have hp := OXModule.skyscraperPOM_presheaf_obj_eq x N U hx
      have hq : (skyscraperPresheaf x
          ((forget₂ (ModuleCat _) AddCommGrpCat).obj N)).obj U = AddCommGrpCat.of (↑N) := by
        simp [skyscraperPresheaf, hx]
      exact eqToIso (hp.trans hq.symm)
    · have hP : IsTerminal ((OXModule.skyscraperPOM x N).presheaf.obj U) := by
        change IsTerminal ((forget₂ (ModuleCat _) AddCommGrpCat).obj
          (OXModule.skyscraperObj x N U))
        rw [OXModule.skyscraperObj, dite_eq_right hx]
        change IsTerminal (AddCommGrpCat.of PUnit)
        letI : ∀ Y : AddCommGrpCat, Unique (Y ⟶ AddCommGrpCat.of PUnit) := fun Y =>
          { default := AddCommGrpCat.ofHom (0 : (↑Y) →+ PUnit)
            uniq := fun f => by ext y }
        exact IsTerminal.ofUnique _
      have hQ : IsTerminal ((skyscraperPresheaf x
          ((forget₂ (ModuleCat _) AddCommGrpCat).obj N)).obj U) := by
        simpa [skyscraperPresheaf, hx] using
          (terminalIsTerminal (C := AddCommGrpCat))
      exact hP.uniqueUpToIso hQ
  · intro U V i
    by_cases hxV : x ∈ V.unop
    · have hxU : x ∈ U.unop := (leOfHom i.unop) hxV
      simp only [dite_eq_left hxV, dite_eq_left hxU]
      rw [OXModule.skyscraperPOM_presheaf_map_eq x N i hxV]
      simp only [skyscraperPresheaf_map, dite_eq_left hxV,
        eqToIso.hom, eqToHom_trans]
      exact (eqToHom_trans _ _).symm
    · have hQ : IsTerminal ((skyscraperPresheaf x
          ((forget₂ (ModuleCat _) AddCommGrpCat).obj N)).obj V) := by
        simpa [skyscraperPresheaf, hxV] using
          (terminalIsTerminal (C := AddCommGrpCat))
      simp only [dite_eq_right hxV]
      apply hQ.hom_ext

/-- The skyscraper presheaf of modules at `x` is a sheaf. -/
private lemma skyscraperPOM_isSheaf (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X.carrier)
      (OXModule.skyscraperPOM x N).presheaf := by
  classical
  exact TopCat.Presheaf.isSheaf_of_iso (skyscraperPOM_underlyingIso X x N).symm
    (skyscraperPresheaf_isSheaf x
      ((forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).obj N))

/-- The skyscraper presheaf of modules has subsingleton sections over an open not containing `x`. -/
private lemma subsingleton_skyscraperObj_of_notMem {X : Scheme.{u}} (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (U : (Opens X.carrier)ᵒᵖ) (hx : x ∉ U.unop) :
    Subsingleton (↑(OXModule.skyscraperObj x N U)) := by
  rw [OXModule.skyscraperObj, dite_eq_right hx]
  infer_instance

/-- The skyscraper presheaf of modules at `x`, as a functor from modules over the local ring. -/
private noncomputable def skyscraperPOMFunctor (X : Scheme.{u}) (x : X) :
    ModuleCat.{u} (X.presheaf.stalk x) ⥤
      PresheafOfModules ((OXModule.ringSheaf X.toRingedSpace).obj) where
  obj := OXModule.skyscraperPOM x
  map f := OXModule.skyscraperPOMMap x f
  map_id N := by
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    ext y
    by_cases hx : x ∈ U.unop
    · simp [OXModule.skyscraperPOMMap, OXModule.skyscraperMapHomApp, hx]
      rfl
    · exact (subsingleton_skyscraperObj_of_notMem x N U hx).elim _ _
  map_comp {N N' N''} (f : N ⟶ N') (g : N' ⟶ N'') := by
    apply PresheafOfModules.hom_ext
    intro U
    by_cases hx : x ∈ U.unop
    -- Both sides are rewritten into `ModuleCat ((X.presheaf ⋙ forget₂ CommRingCat RingCat).obj U)`,
    -- which is the category `OXModule.skyscraperMapHomApp` is stated in; the composite coming
    -- from `PresheafOfModules.comp_app` lands in the `(ringSheaf X).obj.obj U` spelling instead,
    -- and `Category.assoc` cannot cross between the two.
    · change OXModule.skyscraperMapHomApp x (f ≫ g) U =
        OXModule.skyscraperMapHomApp x f U ≫ OXModule.skyscraperMapHomApp x g U
      simp only [OXModule.skyscraperMapHomApp, dite_eq_left hx, Functor.map_comp,
        Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    · apply ModuleCat.hom_ext
      ext y
      exact (subsingleton_skyscraperObj_of_notMem x N'' U hx).elim _ _

/-- The sheafification of the skyscraper presheaf of modules at `x`. -/
private noncomputable def skyscraperModuleFunctor (X : Scheme.{u}) (x : X) :
    ModuleCat.{u} (X.presheaf.stalk x) ⥤ OXModule X.toRingedSpace :=
  skyscraperPOMFunctor X x ⋙ OXModule.sheafify

/-- The skyscraper sheaf of modules at `x`, built directly from the skyscraper presheaf using
that it is already a sheaf. -/
private noncomputable def skyscraperModuleSheafFunctor (X : Scheme.{u}) (x : X) :
    ModuleCat.{u} (X.presheaf.stalk x) ⥤ OXModule X.toRingedSpace where
  obj N := by
    classical
    exact ⟨OXModule.skyscraperPOM x N, skyscraperPOM_isSheaf X x N⟩
  map f := ⟨skyscraperPOMFunctor X x |>.map f⟩
  map_id N := by
    apply SheafOfModules.hom_ext
    exact (skyscraperPOMFunctor X x).map_id N
  map_comp f g := by
    apply SheafOfModules.hom_ext
    exact (skyscraperPOMFunctor X x).map_comp f g

/-- The germ at `x` of a section of `F`, as an element of the stalk in the spelling the functor
`stalkAt X x` produces.

`(stalkAt X x).obj F` and `TopCat.Presheaf.stalk F.val.presheaf x` are the same object, but
identifying them needs two non-reducible unfoldings, so a goal that mixes the two spellings is
not type-correct at `implicit` transparency and `rw` refuses to fire in it. Every statement below
that is later rewritten with therefore uses this name. -/
private noncomputable def stalkGerm (X : Scheme.{u}) (x : X) (F : OXModule X.toRingedSpace)
    (V : Opens X.carrier) (hx : x ∈ V) (m : F.val.obj (op V)) : (stalkAt X x).obj F :=
  TopCat.Presheaf.germ F.val.presheaf V x hx m

/-- Every element of the stalk of `F` at `x` is the germ of a section on some neighbourhood. -/
private lemma exists_stalkGerm (X : Scheme.{u}) (x : X) (F : OXModule X.toRingedSpace)
    (z : (stalkAt X x).obj F) :
    ∃ (V : Opens X.carrier) (hx : x ∈ V) (m : F.val.obj (op V)), stalkGerm X x F V hx m = z := by
  obtain ⟨V, hx, m, h⟩ := TopCat.Presheaf.exists_germ_eq F.val.presheaf z
  exact ⟨V, hx, m, h⟩

/-- A map out of the stalk of `F` at `x`, read as a map out of the stalk of the underlying
`AddCommGrp`-valued presheaf of `F`.

`OXModule.stalk F x` is `TopCat.Presheaf.stalk F.val.presheaf x` carrying a module structure, but
identifying the two bundled objects needs structure eta through `colimit`, whose cocone Mathlib
does not expose. Ascribing the type here performs that identification once, at elaboration. -/
private noncomputable def stalkToSkyscraperAdd (X : Scheme.{u}) (x : X)
    (F : OXModule X.toRingedSpace) (N : ModuleCat.{u} (X.presheaf.stalk x))
    (f : (stalkAt X x).obj F ⟶ N) :
    TopCat.Presheaf.stalk F.val.presheaf x ⟶
      (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).obj N :=
  (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).map f

/-- The map of underlying `AddCommGrp`-valued presheaves from `F` into the skyscraper presheaf of
modules at `x` determined by a map `f` out of the stalk of `F` at `x`: on an open containing `x`
it is `f` after the germ map, and zero elsewhere. -/
private noncomputable def stalkToSkyscraperPsh (X : Scheme.{u}) (x : X)
    (F : OXModule X.toRingedSpace) (N : ModuleCat.{u} (X.presheaf.stalk x))
    (f : (stalkAt X x).obj F ⟶ N) :
    F.val.presheaf ⟶ (OXModule.skyscraperPOM x N).presheaf where
  app U := if h : x ∈ U.unop then
      TopCat.Presheaf.germ F.val.presheaf U.unop x h ≫ stalkToSkyscraperAdd X x F N f ≫
        eqToHom (OXModule.skyscraperPOM_presheaf_obj_eq x N U h).symm
    else 0
  naturality := by
    classical
    rintro ⟨U⟩ ⟨W⟩ i
    by_cases hxW : x ∈ W
    · have hxU : x ∈ U := (leOfHom i.unop) hxW
      simp only [unop_op, dite_eq_left hxW, dite_eq_left hxU]
      rw [OXModule.skyscraperPOM_presheaf_map_eq x N i hxW, ← Category.assoc,
        TopCat.Presheaf.germ_res' F.val.presheaf i x hxW]
      simp only [Category.assoc, eqToHom_trans]
    · apply AddCommGrpCat.hom_ext
      ext m
      exact (subsingleton_skyscraperObj_of_notMem x N (op W) hxW).elim _ _

/-- On an open containing `x`, the map above is the germ map followed by `f`. -/
private lemma stalkToSkyscraperPsh_app_of_mem (X : Scheme.{u}) (x : X)
    (F : OXModule X.toRingedSpace) (N : ModuleCat.{u} (X.presheaf.stalk x))
    (f : (stalkAt X x).obj F ⟶ N) (U : (Opens X.carrier)ᵒᵖ) (hx : x ∈ U.unop) :
    (stalkToSkyscraperPsh X x F N f).app U =
      TopCat.Presheaf.germ F.val.presheaf U.unop x hx ≫ stalkToSkyscraperAdd X x F N f ≫
        eqToHom (OXModule.skyscraperPOM_presheaf_obj_eq x N U hx).symm := by
  simp only [stalkToSkyscraperPsh, dite_eq_left hx]

/-- The map above sends the germ of a section to the value of `f` on that germ. -/
private lemma stalkToSkyscraperPsh_germ (X : Scheme.{u}) (x : X)
    (F : OXModule X.toRingedSpace) (N : ModuleCat.{u} (X.presheaf.stalk x))
    (f : (stalkAt X x).obj F ⟶ N) (V : Opens X.carrier) (hx : x ∈ V)
    (m : F.val.obj (op V)) :
    (eqToHom (OXModule.skyscraperPOM_presheaf_obj_eq x N (op V) hx))
        ((stalkToSkyscraperPsh X x F N f).app (op V) m) =
      f.hom (stalkGerm X x F V hx m) := by
  show ((stalkToSkyscraperPsh X x F N f).app (op V) ≫
    eqToHom (OXModule.skyscraperPOM_presheaf_obj_eq x N (op V) hx)) m = _
  rw [stalkToSkyscraperPsh_app_of_mem X x F N f (op V) hx]
  simp only [unop_op, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  rfl

/-- The same map, with its codomain spelled as the underlying presheaf of the skyscraper
**sheaf**: that is the form `PresheafOfModules.homMk` asks for, while the naturality proof above
needs the `OXModule.skyscraperPOM` spelling that Tag08BQ's rewrite rules are stated at. -/
private noncomputable def stalkToSkyscraperSheafPsh (X : Scheme.{u}) (x : X)
    (F : OXModule X.toRingedSpace) (N : ModuleCat.{u} (X.presheaf.stalk x))
    (f : (stalkAt X x).obj F ⟶ N) :
    F.val.presheaf ⟶ ((skyscraperModuleSheafFunctor X x).obj N).val.presheaf :=
  stalkToSkyscraperPsh X x F N f

private lemma stalkToSkyscraperSheafPsh_germ (X : Scheme.{u}) (x : X)
    (F : OXModule X.toRingedSpace) (N : ModuleCat.{u} (X.presheaf.stalk x))
    (f : (stalkAt X x).obj F ⟶ N) (V : Opens X.carrier) (hx : x ∈ V)
    (m : F.val.obj (op V)) :
    (eqToHom (OXModule.skyscraperPOM_presheaf_obj_eq x N (op V) hx))
        ((stalkToSkyscraperSheafPsh X x F N f).app (op V) m) =
      f.hom (stalkGerm X x F V hx m) :=
  stalkToSkyscraperPsh_germ X x F N f V hx m

/-- A map from the stalk of `F` at `x` into `N` gives a map of sheaves of modules from `F` into
the skyscraper at `x` with fibre `N`. -/
private noncomputable def moduleHomFromStalkToSkyscraper
    (X : Scheme.{u}) (x : X) (F : OXModule X.toRingedSpace)
    (N : ModuleCat.{u} (X.presheaf.stalk x))
    (f : (stalkAt X x).obj F ⟶ N) :
    F ⟶ (skyscraperModuleSheafFunctor X x).obj N := by
  classical
  refine ⟨PresheafOfModules.homMk (stalkToSkyscraperSheafPsh X x F N f) ?_⟩
  rintro ⟨V⟩ r m
  by_cases hx : x ∈ V
  · apply (ConcreteCategory.bijective_of_isIso
      (eqToHom (OXModule.skyscraperPOM_presheaf_obj_eq x N (op V) hx))).injective
    -- Term mode throughout: once `germ` has been applied to `r • m`, the goal is no longer
    -- type-correct at `implicit` transparency and no further `rw` can fire.
    refine (stalkToSkyscraperSheafPsh_germ X x F N f V hx (r • m)).trans ?_
    refine Eq.trans ?_ (OXModule.skyscraperPOM_leg_smul x N (op V) hx r
      ((stalkToSkyscraperSheafPsh X x F N f).app (op V) m)).symm
    refine Eq.trans ?_ (congrArg
      (fun z => (ConcreteCategory.hom (X.presheaf.germ V x hx)) r • z)
      (stalkToSkyscraperSheafPsh_germ X x F N f V hx m).symm)
    change f.hom (TopCat.Presheaf.germ F.val.presheaf V x hx (r • m)) = _
    exact (congrArg f.hom
      (PresheafOfModules.germ_smul (R := X.presheaf) F.val x V hx r m)).trans
      (map_smul f.hom _ _)
  · exact (subsingleton_skyscraperObj_of_notMem x N (op V) hx).elim _ _

/-- On an open containing `x`, the map into the skyscraper built from `f` has the value `f` would
give on a germ. -/
private lemma moduleHomFromStalkToSkyscraper_app (X : Scheme.{u}) (x : X)
    (F : OXModule X.toRingedSpace) (N : ModuleCat.{u} (X.presheaf.stalk x))
    (f : (stalkAt X x).obj F ⟶ N) (V : Opens X.carrier) (hx : x ∈ V)
    (m : F.val.obj (op V)) :
    (eqToHom (OXModule.skyscraperPOM_presheaf_obj_eq x N (op V) hx))
        (((moduleHomFromStalkToSkyscraper X x F N f).val.app (op V)) m) =
      f.hom (stalkGerm X x F V hx m) :=
  stalkToSkyscraperSheafPsh_germ X x F N f V hx m

/-- The stalk at `x` of the skyscraper at `x` with fibre `N` is `N`. -/
private noncomputable def skyscraperStalkIso (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) :
    (stalkAt X x).obj ((skyscraperModuleSheafFunctor X x).obj N) ≅ N :=
  OXModule.sheafify_skyscraperPOM_stalkIso_skyscraper x N

/-- The identification of the stalk of the skyscraper with its fibre, on underlying groups, at
the spelling the skyscraper **sheaf** functor produces. -/
private noncomputable def skyscraperStalkAddEquiv (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) :
    ↑((stalkAt X x).obj ((skyscraperModuleSheafFunctor X x).obj N)) ≃+ N :=
  OXModule.sheafify_skyscraperPOM_stalkIso_skyscraper_addEquiv x N

private lemma skyscraperStalkAddEquiv_germ (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (V : Opens X.carrier) (hx : x ∈ V)
    (n : ((skyscraperModuleSheafFunctor X x).obj N).val.obj (op V)) :
    skyscraperStalkAddEquiv X x N
        (stalkGerm X x ((skyscraperModuleSheafFunctor X x).obj N) V hx n) =
      (eqToHom (OXModule.skyscraperPOM_presheaf_obj_eq x N (op V) hx)) n :=
  OXModule.sheafify_skyscraperPOM_stalkIso_skyscraper_addEquiv_germ x N (op V) hx n

private lemma skyscraperStalkIso_hom_apply (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x))
    (z : (stalkAt X x).obj ((skyscraperModuleSheafFunctor X x).obj N)) :
    (skyscraperStalkIso X x N).hom.hom z = skyscraperStalkAddEquiv X x N z := rfl

/-- A map of sheaves of modules from `F` into the skyscraper at `x` gives a map from the stalk of
`F` at `x`. -/
private noncomputable def moduleHomToStalk (X : Scheme.{u}) (x : X)
    (F : OXModule X.toRingedSpace)
    (N : ModuleCat.{u} (X.presheaf.stalk x))
    (g : F ⟶ (skyscraperModuleSheafFunctor X x).obj N) :
    (stalkAt X x).obj F ⟶ N :=
  (stalkAt X x).map g ≫ (skyscraperStalkIso X x N).hom

/-- The map out of the stalk determined by `g` reads a germ off the component of `g`. -/
private lemma moduleHomToStalk_germ (X : Scheme.{u}) (x : X)
    (F : OXModule X.toRingedSpace) (N : ModuleCat.{u} (X.presheaf.stalk x))
    (g : F ⟶ (skyscraperModuleSheafFunctor X x).obj N) (V : Opens X.carrier) (hx : x ∈ V)
    (m : F.val.obj (op V)) :
    (moduleHomToStalk X x F N g).hom (stalkGerm X x F V hx m) =
      (eqToHom (OXModule.skyscraperPOM_presheaf_obj_eq x N (op V) hx)) (g.val.app (op V) m) := by
  show (OXModule.sheafify_skyscraperPOM_stalkIso_skyscraper_addEquiv x N)
    (OXModule.stalkMapAdd F ((skyscraperModuleSheafFunctor X x).obj N) g x
      (TopCat.Presheaf.germ F.val.presheaf V x hx m)) = _
  -- Term mode: the goal mixes `F.val.obj U` with `((toPresheaf _).obj F.val).obj U`, so it is
  -- not type-correct at `implicit` transparency and `rw` refuses to fire in it.
  refine Eq.trans (congrArg
      (fun z : ↑(TopCat.Presheaf.stalk (OXModule.skyscraperPOM x N).presheaf x) =>
        (OXModule.sheafify_skyscraperPOM_stalkIso_skyscraper_addEquiv x N) z)
      (OXModule.stalkMapAdd_germ F ((skyscraperModuleSheafFunctor X x).obj N) g x V hx m)) ?_
  exact OXModule.sheafify_skyscraperPOM_stalkIso_skyscraper_addEquiv_germ x N (op V) hx _

/-- Maps out of the stalk at `x` correspond to maps into the skyscraper at `x`. -/
private noncomputable def moduleStalkHomEquiv (X : Scheme.{u}) (x : X)
    (F : OXModule X.toRingedSpace) (N : ModuleCat.{u} (X.presheaf.stalk x)) :
    ((stalkAt X x).obj F ⟶ N) ≃
      (F ⟶ (skyscraperModuleSheafFunctor X x).obj N) where
  toFun := moduleHomFromStalkToSkyscraper X x F N
  invFun := moduleHomToStalk X x F N
  left_inv f := by
    classical
    apply ModuleCat.hom_ext
    ext z
    obtain ⟨V, hx, m, rfl⟩ := exists_stalkGerm X x F z
    rw [moduleHomToStalk_germ]
    exact moduleHomFromStalkToSkyscraper_app X x F N f V hx m
  right_inv g := by
    classical
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    rintro ⟨V⟩
    apply ModuleCat.hom_ext
    ext m
    by_cases hx : x ∈ V
    · apply (ConcreteCategory.bijective_of_isIso
        (eqToHom (OXModule.skyscraperPOM_presheaf_obj_eq x N (op V) hx))).injective
      rw [moduleHomFromStalkToSkyscraper_app X x F N (moduleHomToStalk X x F N g) V hx m,
        moduleHomToStalk_germ X x F N g V hx m]
    · exact (subsingleton_skyscraperObj_of_notMem x N (op V) hx).elim _ _

/-- The identification of the stalk of a skyscraper with its fibre is natural in the fibre. -/
private lemma skyscraperStalkIso_naturality (X : Scheme.{u}) (x : X)
    {N N' : ModuleCat.{u} (X.presheaf.stalk x)} (f : N ⟶ N') :
    (stalkAt X x).map ((skyscraperModuleSheafFunctor X x).map f) ≫
      (skyscraperStalkIso X x N').hom = (skyscraperStalkIso X x N).hom ≫ f := by
  classical
  apply ModuleCat.hom_ext
  ext z
  obtain ⟨V, hx, m, rfl⟩ :=
    exists_stalkGerm X x ((skyscraperModuleSheafFunctor X x).obj N) z
  show (moduleHomToStalk X x ((skyscraperModuleSheafFunctor X x).obj N) N'
      ((skyscraperModuleSheafFunctor X x).map f)).hom
      (stalkGerm X x ((skyscraperModuleSheafFunctor X x).obj N) V hx m) =
    f.hom (skyscraperStalkAddEquiv X x N
      (stalkGerm X x ((skyscraperModuleSheafFunctor X x).obj N) V hx m))
  rw [moduleHomToStalk_germ, skyscraperStalkAddEquiv_germ]
  exact OXModule.skyscraperPOMMap_presheaf_app_eq x f (op V) hx m

/-- The stalk functor at `x` is left adjoint to the skyscraper functor at `x`. -/
private noncomputable def moduleStalkAdjunction (X : Scheme.{u}) (x : X) :
    stalkAt X x ⊣ skyscraperModuleSheafFunctor X x :=
  Adjunction.mkOfHomEquiv {
    homEquiv := moduleStalkHomEquiv X x
    homEquiv_naturality_left_symm := by
      intro F' F N f g
      change (stalkAt X x).map (f ≫ g) ≫ _ = _
      rw [Functor.map_comp, Category.assoc]
      rfl
    homEquiv_naturality_right := by
      intro F N N' f g
      apply (moduleStalkHomEquiv X x F N').symm.injective
      rw [Equiv.symm_apply_apply]
      change f ≫ g = (stalkAt X x).map
        (moduleStalkHomEquiv X x F N f ≫ (skyscraperModuleSheafFunctor X x).map g) ≫ _
      rw [Functor.map_comp, Category.assoc, skyscraperStalkIso_naturality, ← Category.assoc]
      change f ≫ g = (moduleStalkHomEquiv X x F N).symm
        (moduleStalkHomEquiv X x F N f) ≫ g
      rw [Equiv.symm_apply_apply] }

/-- The underlying-sheaf-of-abelian-groups functor, with `TopCat.Sheaf` as its codomain.

`TopCat.Sheaf C Y` and `CategoryTheory.Sheaf (Opens.grothendieckTopology Y) C` are the same type
but carry two different `Category` instances, and typeclass resolution — which works at reducible
transparency — cannot cross between them. `SheafOfModules.toSheaf` is stated over the second
spelling while `TopCat.Sheaf.forget` and `TopCat.Presheaf.stalkFunctor` are stated over the first,
so the composite below is given a name at the first spelling once, here, and every instance for it
is transported across in term mode. -/
private noncomputable def toUnderlyingSheaf (X : Scheme.{u}) :
    OXModule X.toRingedSpace ⥤ TopCat.Sheaf AddCommGrpCat.{u} X.toPresheafedSpace :=
  SheafOfModules.toSheaf (OXModule.ringSheaf X.toRingedSpace)

private lemma toUnderlyingSheaf_preservesFiniteLimits (X : Scheme.{u}) :
    PreservesFiniteLimits (toUnderlyingSheaf X) :=
  (inferInstance : PreservesFiniteLimits
    (SheafOfModules.toSheaf (OXModule.ringSheaf X.toRingedSpace)))

private lemma toUnderlyingSheaf_additive (X : Scheme.{u}) :
    (toUnderlyingSheaf X).Additive :=
  (inferInstance : (SheafOfModules.toSheaf (OXModule.ringSheaf X.toRingedSpace)).Additive)

/-- The stalk at `x` of the underlying sheaf of abelian groups. -/
private noncomputable def underlyingStalkFunctor (X : Scheme.{u}) (x : X) :
    OXModule X.toRingedSpace ⥤ AddCommGrpCat.{u} :=
  toUnderlyingSheaf X ⋙ (TopCat.Sheaf.forget AddCommGrpCat.{u} X.toPresheafedSpace ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)

private lemma underlyingStalkFunctor_preservesFiniteLimits (X : Scheme.{u}) (x : X) :
    PreservesFiniteLimits (underlyingStalkFunctor X x) := by
  have := toUnderlyingSheaf_preservesFiniteLimits X
  exact comp_preservesFiniteLimits (toUnderlyingSheaf X)
    (TopCat.Sheaf.forget AddCommGrpCat.{u} X.toPresheafedSpace ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)

private lemma underlyingStalkFunctor_additive (X : Scheme.{u}) (x : X) :
    (underlyingStalkFunctor X x).Additive := by
  have := toUnderlyingSheaf_additive X
  have : (toUnderlyingSheaf X ⋙ (TopCat.Sheaf.forget AddCommGrpCat.{u} X.toPresheafedSpace ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)).Additive := inferInstance
  exact this

/-- The underlying sheaf of abelian groups of the stalk functor is the stalk of the underlying
sheaf. -/
private noncomputable def stalkAtUnderlyingIso (X : Scheme.{u}) (x : X) :
    stalkAt X x ⋙ forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat ≅
      underlyingStalkFunctor X x :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- The stalk functor at `x` preserves finite limits. -/
private lemma stalkAt_preservesFiniteLimits (X : Scheme.{u}) (x : X) :
    PreservesFiniteLimits (stalkAt X x) := by
  have := underlyingStalkFunctor_preservesFiniteLimits X x
  let U := forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat
  have : PreservesFiniteLimits (stalkAt X x ⋙ U) :=
    preservesFiniteLimits_of_natIso (stalkAtUnderlyingIso X x).symm
  exact preservesFiniteLimits_of_reflects_of_preserves (stalkAt X x) U

/-- The stalk functor at `x` is additive. -/
private lemma stalkAt_additive (X : Scheme.{u}) (x : X) :
    (stalkAt X x).Additive := by
  have := underlyingStalkFunctor_additive X x
  let U := forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat
  have : (stalkAt X x ⋙ U).Additive :=
    Functor.additive_of_iso (stalkAtUnderlyingIso X x).symm
  exact Functor.additive_of_comp_faithful _ U

/-- Restriction of scalars along the germ map at `x`, with the ring of sections written as
`(OXModule.ringSheaf X.toRingedSpace).obj.obj U`.

That is the spelling `PresheafOfModules.evaluation (OXModule.ringSheaf X.toRingedSpace).obj U`
lands in, whereas
`ModuleCat.restrictScalars` is stated over `X.presheaf.obj U` in `CommRingCat`. The two are the
same ring but reach their `Ring` instance by different non-reducible routes, so the functor is
named here once at the former spelling and its instances are transported in term mode. -/
private noncomputable def skyscraperRestrictScalars (X : Scheme.{u}) (x : X)
    (U : (Opens X.carrier)ᵒᵖ) (hx : x ∈ U.unop) :
    ModuleCat.{u} (X.presheaf.stalk x) ⥤
      ModuleCat.{u} ((OXModule.ringSheaf X.toRingedSpace).obj.obj U) :=
  ModuleCat.restrictScalars (X.presheaf.germ U.unop x hx).hom

private lemma skyscraperRestrictScalars_additive (X : Scheme.{u}) (x : X)
    (U : (Opens X.carrier)ᵒᵖ) (hx : x ∈ U.unop) :
    (skyscraperRestrictScalars X x U hx).Additive :=
  (inferInstance :
    (ModuleCat.restrictScalars (X.presheaf.germ U.unop x hx).hom).Additive)

private lemma skyscraperRestrictScalars_preservesFiniteColimits (X : Scheme.{u}) (x : X)
    (U : (Opens X.carrier)ᵒᵖ) (hx : x ∈ U.unop) :
    PreservesFiniteColimits (skyscraperRestrictScalars X x U hx) :=
  (inferInstance : PreservesFiniteColimits
    (ModuleCat.restrictScalars (X.presheaf.germ U.unop x hx).hom))

/-- On an open containing `x`, the value of the skyscraper presheaf of modules is `N` with
scalars restricted along the germ map. -/
private lemma skyscraperObj_eq (X : Scheme.{u}) (x : X) (U : (Opens X.carrier)ᵒᵖ)
    (hx : x ∈ U.unop) (N : ModuleCat.{u} (X.presheaf.stalk x)) :
    OXModule.skyscraperObj x N U =
      (ModuleCat.restrictScalars (X.presheaf.germ U.unop x hx).hom).obj N := by
  rw [OXModule.skyscraperObj, dite_eq_left hx]

/-- On an open containing `x`, evaluating the skyscraper presheaf of modules is restriction of
scalars along the germ map. -/
private noncomputable def skyscraperEvaluationIso (X : Scheme.{u}) (x : X)
    (U : (Opens X.carrier)ᵒᵖ) (hx : x ∈ U.unop) :
    skyscraperPOMFunctor X x ⋙
        PresheafOfModules.evaluation (OXModule.ringSheaf X.toRingedSpace).obj U ≅
      skyscraperRestrictScalars X x U hx := by
  refine NatIso.ofComponents (fun N => eqToIso (skyscraperObj_eq X x U hx N)) ?_
  intro N N' f
  change OXModule.skyscraperMapHomApp x f U ≫ eqToHom (skyscraperObj_eq X x U hx N')
    = eqToHom (skyscraperObj_eq X x U hx N)
      ≫ (ModuleCat.restrictScalars (X.presheaf.germ U.unop x hx).hom).map f
  rw [OXModule.skyscraperMapHomApp, dite_eq_left hx]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- The skyscraper presheaf functor at `x` is additive. -/
private lemma skyscraperPOMFunctor_additive (X : Scheme.{u}) (x : X) :
    (skyscraperPOMFunctor X x).Additive := by
  constructor
  intro N N' f g
  apply PresheafOfModules.hom_ext
  intro U
  by_cases hx : x ∈ U.unop
  · have := skyscraperRestrictScalars_additive X x U hx
    have := Functor.additive_of_iso (skyscraperEvaluationIso X x U hx).symm
    exact Functor.map_add (skyscraperPOMFunctor X x ⋙
      PresheafOfModules.evaluation (OXModule.ringSheaf X.toRingedSpace).obj U) (f := f) (g := g)
  · apply ModuleCat.hom_ext
    ext m
    exact (subsingleton_skyscraperObj_of_notMem x N' U hx).elim _ _

/-- The skyscraper presheaf functor at `x` preserves finite colimits. -/
private lemma skyscraperPOMFunctor_preservesFiniteColimits (X : Scheme.{u}) (x : X) :
    PreservesFiniteColimits (skyscraperPOMFunctor X x) where
  preservesFiniteColimits J := {
    preservesColimit := fun {K} => {
      preserves := fun {c} hc => ⟨by
        apply PresheafOfModules.evaluationJointlyReflectsColimits
        intro U
        have : PreservesFiniteColimits (skyscraperPOMFunctor X x ⋙
            PresheafOfModules.evaluation (OXModule.ringSheaf X.toRingedSpace).obj U) := by
          by_cases hx : x ∈ U.unop
          · have := skyscraperRestrictScalars_preservesFiniteColimits X x U hx
            exact preservesFiniteColimits_of_natIso (skyscraperEvaluationIso X x U hx).symm
          · let G := skyscraperPOMFunctor X x ⋙
              PresheafOfModules.evaluation (OXModule.ringSheaf X.toRingedSpace).obj U
            have hG : IsZero G := G.isZero (fun N => by
              show IsZero (OXModule.skyscraperObj x N U)
              exact ModuleCat.isZero_iff_subsingleton.mpr
                (subsingleton_skyscraperObj_of_notMem x N U hx))
            have := G.preservesColimitsOfSize_of_isZero hG
            infer_instance
        exact isColimitOfPreserves (skyscraperPOMFunctor X x ⋙
          PresheafOfModules.evaluation (OXModule.ringSheaf X.toRingedSpace).obj U) hc⟩ } }

/-- Restricting scalars along the identity leaves a functor into presheaves of modules
unchanged.

Stated for an arbitrary `H` on purpose: the identification is then checked once against an
opaque `H.obj N`, where it is immediate, instead of once per object against a skyscraper whose
`dite` would be unfolded in full. -/
private lemma comp_restrictScalarsId (X : Scheme.{u}) {D : Type*} [Category.{u} D]
    (H : D ⥤ PresheafOfModules.{u} ((OXModule.ringSheaf X.toRingedSpace).obj)) :
    H ⋙ PresheafOfModules.restrictScalars (𝟙 (OXModule.ringSheaf X.toRingedSpace).obj) = H :=
  rfl

/-- The underlying presheaf of modules of the skyscraper sheaf is the skyscraper presheaf. -/
private lemma skyscraperModuleSheafFunctor_comp_forget (X : Scheme.{u}) (x : X) :
    skyscraperModuleSheafFunctor X x ⋙ SheafOfModules.forget (OXModule.ringSheaf X.toRingedSpace)
      = skyscraperPOMFunctor X x := rfl

/-- The skyscraper sheaf functor, followed by the right adjoint of sheafification and then by
sheafification itself, is the sheafified skyscraper presheaf functor.

This is the shape the counit of `PresheafOfModules.sheafificationAdjunction` is stated at, so
having it as an equality of functors makes the comparison isomorphism below an `eqToIso` with no
naturality obligation. -/
private lemma skyscraperModuleFunctor_eq (X : Scheme.{u}) (x : X) :
    skyscraperModuleSheafFunctor X x ⋙
        ((SheafOfModules.forget (OXModule.ringSheaf X.toRingedSpace) ⋙
            PresheafOfModules.restrictScalars (𝟙 (OXModule.ringSheaf X.toRingedSpace).obj)) ⋙
          PresheafOfModules.sheafification (𝟙 (OXModule.ringSheaf X.toRingedSpace).obj))
      = skyscraperModuleFunctor X x := by
  rw [← Functor.assoc, ← Functor.assoc, comp_restrictScalarsId X,
    skyscraperModuleSheafFunctor_comp_forget]
  rfl

/-- The sheafification of the skyscraper presheaf agrees with the skyscraper sheaf. -/
private noncomputable def skyscraperSheafificationIso (X : Scheme.{u}) (x : X) :
    skyscraperModuleFunctor X x ≅ skyscraperModuleSheafFunctor X x :=
  eqToIso (skyscraperModuleFunctor_eq X x).symm ≪≫
    Functor.isoWhiskerLeft (skyscraperModuleSheafFunctor X x)
      (asIso (PresheafOfModules.sheafificationAdjunction
        (R := OXModule.ringSheaf X.toRingedSpace)
        (𝟙 (OXModule.ringSheaf X.toRingedSpace).obj)).counit) ≪≫
    (skyscraperModuleSheafFunctor X x).rightUnitor

/-- Sheafification of presheaves of `𝒪_X`-modules preserves finite colimits, being a left
adjoint. `OXModule.sheafify` is a name for it, which typeclass resolution cannot see through,
so the instance is transported here in term mode. -/
private lemma sheafify_preservesFiniteColimits (X : Scheme.{u}) :
    PreservesFiniteColimits (OXModule.sheafify (X := X.toRingedSpace)) :=
  (inferInstance : PreservesFiniteColimits
    (PresheafOfModules.sheafification (R := OXModule.ringSheaf X.toRingedSpace)
      (𝟙 (OXModule.ringSheaf X.toRingedSpace).obj)))

/-- The skyscraper sheaf functor at `x` preserves finite colimits. -/
private lemma skyscraperModuleSheafFunctor_preservesFiniteColimits
    (X : Scheme.{u}) (x : X) :
    PreservesFiniteColimits (skyscraperModuleSheafFunctor X x) := by
  have := skyscraperPOMFunctor_preservesFiniteColimits X x
  have := sheafify_preservesFiniteColimits X
  have : PreservesFiniteColimits (skyscraperModuleFunctor X x) :=
    comp_preservesFiniteColimits (skyscraperPOMFunctor X x)
      (OXModule.sheafify (X := X.toRingedSpace))
  exact preservesFiniteColimits_of_natIso (skyscraperSheafificationIso X x)

/-- The skyscraper sheaf functor at `x` is additive. -/
private lemma skyscraperModuleSheafFunctor_additive (X : Scheme.{u}) (x : X) :
    (skyscraperModuleSheafFunctor X x).Additive := by
  have := skyscraperPOMFunctor_additive X x
  constructor
  intro N N' f g
  apply SheafOfModules.hom_ext
  exact Functor.map_add (skyscraperPOMFunctor X x)


/-- The stalk functor at `x` preserves finite colimits, being a left adjoint. -/
private lemma stalkAt_preservesFiniteColimits (X : Scheme.{u}) (x : X) :
    PreservesFiniteColimits (stalkAt X x) := by
  have := (moduleStalkAdjunction X x).isLeftAdjoint
  infer_instance

/-- The skyscraper sheaf functor at `x` preserves finite limits, being a right adjoint. -/
private lemma skyscraperModuleSheafFunctor_preservesFiniteLimits (X : Scheme.{u}) (x : X) :
    PreservesFiniteLimits (skyscraperModuleSheafFunctor X x) := by
  have := (moduleStalkAdjunction X x).isRightAdjoint
  infer_instance

attribute [local instance] stalkAt_additive stalkAt_preservesFiniteLimits
  stalkAt_preservesFiniteColimits skyscraperModuleSheafFunctor_additive
  skyscraperModuleSheafFunctor_preservesFiniteLimits
  skyscraperModuleSheafFunctor_preservesFiniteColimits

/-- An exact adjunction of abelian categories induces the corresponding adjunction on
unbounded derived categories. -/
private noncomputable def exactAdjunction_mapDerivedCategory
    {A : Type u} [Category A] [Abelian A] [HasDerivedCategory A]
    {B : Type u} [Category B] [Abelian B] [HasDerivedCategory B]
    {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (adj : G ⊣ F) : G.mapDerivedCategory ⊣ F.mapDerivedCategory := by
  let adjH : G.mapHomotopyCategory (ComplexShape.up ℤ) ⊣
      F.mapHomotopyCategory (ComplexShape.up ℤ) := by
    let adjC : G.mapHomologicalComplex (ComplexShape.up ℤ) ⊣
        F.mapHomologicalComplex (ComplexShape.up ℤ) :=
      CategoryTheory.Adjunction.mapHomologicalComplex adj (ComplexShape.up ℤ)
    refine {
      unit := Quotient.natTransLift _
        (Functor.whiskerRight adjC.unit
          (HomotopyCategory.quotient B (ComplexShape.up ℤ)))
      counit := Quotient.natTransLift _
        (Functor.whiskerRight adjC.counit
          (HomotopyCategory.quotient A (ComplexShape.up ℤ)))
      left_triangle_components := ?_
      right_triangle_components := ?_ }
    · rintro ⟨K⟩
      exact ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map_comp _ _).symm.trans
        ((congrArg _ (adjC.left_triangle_components K)).trans
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map_id _))
    · rintro ⟨K⟩
      exact ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map_comp _ _).symm.trans
        ((congrArg _ (adjC.right_triangle_components K)).trans
          ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map_id _))
  letI : CatCommSq (G.mapHomotopyCategory (ComplexShape.up ℤ))
      (DerivedCategory.Qh (C := B)) (DerivedCategory.Qh (C := A))
      G.mapDerivedCategory := ⟨G.mapDerivedCategoryFactorsh.symm⟩
  letI : CatCommSq (F.mapHomotopyCategory (ComplexShape.up ℤ))
      (DerivedCategory.Qh (C := A)) (DerivedCategory.Qh (C := B))
      F.mapDerivedCategory := ⟨F.mapDerivedCategoryFactorsh.symm⟩
  exact adjH.localization
    (DerivedCategory.Qh (C := B))
    (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))
    (DerivedCategory.Qh (C := A))
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
    G.mapDerivedCategory F.mapDerivedCategory

/-- In a distinguished triangle whose first vertex is bounded above by `a`, the second map is an
isomorphism on cohomology in degrees above `a`. -/
private lemma isIso_homologyMap_of_isLE {C : Type u} [Category C] [Abelian C]
    [HasDerivedCategory C] {L K M : DerivedCategory C} (f : L ⟶ K)
    (g : K ⟶ M) (h : M ⟶ L⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f g h ∈ distTriang (DerivedCategory C)) (i a : ℤ)
    (hi : a < i) [L.IsLE a] : IsIso ((DerivedCategory.homologyFunctor C i).map g) := by
  have h₁ := DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff
    (Triangle.mk f g h) hT i
  have h₂ := DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff
    (Triangle.mk f g h) hT i (i + 1) (by omega)
  dsimp at h₁ h₂
  have : Mono ((DerivedCategory.homologyFunctor C i).map g) := by
    rw [h₁]
    exact (DerivedCategory.isZero_of_isLE L a i hi).eq_of_src _ _
  have : Epi ((DerivedCategory.homologyFunctor C i).map g) := by
    rw [h₂]
    exact (DerivedCategory.isZero_of_isLE L a (i + 1) (by omega)).eq_of_tgt _ _
  exact isIso_of_mono_of_epi _

/-- An object concentrated in degree `i` is its degree-`i` cohomology placed in degree `i`. -/
private lemma nonempty_iso_singleFunctor_obj_homology {C : Type u} [Category C]
    [Abelian C] [HasDerivedCategory C] (Z : DerivedCategory C) (i : ℤ)
    [Z.IsGE i] [Z.IsLE i] :
    Nonempty (Z ≅ (DerivedCategory.singleFunctor C i).obj
      ((DerivedCategory.homologyFunctor C i).obj Z)) := by
  obtain ⟨W, ⟨e⟩⟩ :=
    DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE Z i
  exact ⟨e ≪≫ (DerivedCategory.singleFunctor C i).mapIso
    (((DerivedCategory.homologyFunctor C i).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (C := C) i).app W).symm)⟩

/-- If the cohomology of `K` vanishes above `b`, then morphisms from `K` into an object placed in
a degree above `b` vanish. -/
private lemma hom_subsingleton_of_homology_vanishes_above
    {C : Type u} [Category C] [Abelian C] [HasDerivedCategory C]
    (K : DerivedCategory C) (G : C) (b i : ℤ) (hbi : b < i)
    (hK : ∀ j : ℤ, b < j →
      IsZero ((DerivedCategory.homologyFunctor C j).obj K)) :
    Subsingleton (K ⟶ (DerivedCategory.singleFunctor C i).obj G) := by
  let : K.IsLE b := (DerivedCategory.isLE_iff K b).2 hK
  let : ((DerivedCategory.singleFunctor C i).obj G).IsGE i := inferInstance
  constructor
  intro f g
  exact sub_eq_zero.mp (DerivedCategory.TStructure.t.zero (f - g) b i (by omega))

/-- A bounded derived object admits cohomological bounds. -/
private lemma exists_bounds_of_bounded
    {C : Type u} [Category C] [Abelian C] [HasDerivedCategory C]
    (K : DerivedCategory.Bounded C) :
    ∃ a b : ℤ, K.obj.IsGE a ∧ K.obj.IsLE b := by
  have hbounded := K.property
  change (∃ a : ℤ, K.obj.IsGE a) ∧ (∃ b : ℤ, K.obj.IsLE b) at hbounded
  rcases hbounded with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  exact ⟨a, b, ha, hb⟩

/-- If some cohomology of a bounded object above `b` is nonzero, there is a largest such degree. -/
private lemma exists_top_nonzero_homology_above
    {C : Type u} [Category C] [Abelian C] [HasDerivedCategory C]
    (K : DerivedCategory.Bounded C) (b : ℤ)
    (hnot : ∃ j : ℤ, b < j ∧
      ¬ IsZero ((DerivedCategory.homologyFunctor C j).obj K.obj)) :
    ∃ i : ℤ, b < i ∧
      ¬ IsZero ((DerivedCategory.homologyFunctor C i).obj K.obj) ∧
      ∀ j : ℤ, i < j → IsZero ((DerivedCategory.homologyFunctor C j).obj K.obj) := by
  classical
  obtain ⟨a, c, ha, hc⟩ := exists_bounds_of_bounded K
  let : K.obj.IsGE a := ha
  let : K.obj.IsLE c := hc
  obtain ⟨j, hbj, hnj⟩ := hnot
  have hja : a ≤ j := by
    by_contra h
    exact hnj (DerivedCategory.isZero_of_isGE K.obj a j (by omega))
  have hjc : j ≤ c := by
    by_contra h
    exact hnj (DerivedCategory.isZero_of_isLE K.obj c j (by omega))
  let S : Set ℤ := {k | b < k ∧
    ¬ IsZero ((DerivedCategory.homologyFunctor C k).obj K.obj)}
  have hS : S.Nonempty := ⟨j, hbj, hnj⟩
  have hSub : S ⊆ Set.Icc a c := by
    intro k hk
    constructor
    · by_contra h
      exact hk.2 (DerivedCategory.isZero_of_isGE K.obj a k (by omega))
    · by_contra h
      exact hk.2 (DerivedCategory.isZero_of_isLE K.obj c k (by omega))
  have hFin : S.Finite := (Set.finite_Icc a c).subset hSub
  obtain ⟨i, hiS, hiMax⟩ := hFin.exists_maximal hS
  have hbi : b < i := hiS.1
  refine ⟨i, hiS.1, hiS.2, fun k hik => ?_⟩
  by_contra hnk
  have hkS : k ∈ S := ⟨by omega, hnk⟩
  have hki : k ≤ i := hiMax hkS (le_of_lt hik)
  omega

/-- If a derived object is bounded above at `i`, every nonzero map from its `i`th
cohomology to `G` induces a nonzero map from the derived object to `G` placed in degree `i`. -/
private lemma exists_nonzero_hom_to_single_of_nonzero_homology
    {C : Type u} [Category C] [Abelian C] [HasDerivedCategory C]
    (K : DerivedCategory C) (i : ℤ) (hK : K.IsLE i)
    (G : C) (f : (DerivedCategory.homologyFunctor C i).obj K ⟶ G) (hf : f ≠ 0) :
    ∃ g : K ⟶ (DerivedCategory.singleFunctor C i).obj G, g ≠ 0 := by
  let t := DerivedCategory.TStructure.t (C := C)
  let : t.IsLE K i := hK
  let U := (t.truncLE i).obj K
  let eU : U ≅ K := asIso ((t.truncLEι i).app K)
  let V := (t.truncGE i).obj U
  let p : K ⟶ V := eU.inv ≫ (t.truncGEπ i).app U
  let H := DerivedCategory.homologyFunctor C i
  have hπ : IsIso (H.map ((t.truncGEπ i).app U)) :=
    isIso_homologyMap_of_isLE
      ((t.truncLTι i).app U) ((t.truncGEπ i).app U) ((t.truncGEδLT i).app U)
      (t.triangleLTGE_distinguished i U) i (i - 1) (by omega)
  have := hπ
  let hp : H.obj K ≅ H.obj V :=
    asIso (H.map eU.inv) ≪≫ asIso (H.map ((t.truncGEπ i).app U))
  have : t.IsGE V i := by dsimp [V]; infer_instance
  have : t.IsLE V i := by dsimp [V, U]; infer_instance
  obtain ⟨eV⟩ := nonempty_iso_singleFunctor_obj_homology V i
  let q : H.obj V ⟶ G := hp.inv ≫ f
  have hq : q ≠ 0 := by
    intro h
    have hz := congrArg (fun z => hp.hom ≫ z) h
    apply hf
    simpa [q, Category.assoc] using hz
  have hmap : (DerivedCategory.singleFunctor C i).map q ≠ 0 := by
    intro h
    apply hq
    exact (DerivedCategory.singleFunctor C i).map_injective (by simpa using h)
  have heV : eV.hom ≫ (DerivedCategory.singleFunctor C i).map q ≠ 0 := by
    intro h
    apply hmap
    have := congrArg (fun z => eV.inv ≫ z) h
    simpa using this
  refine ⟨p ≫ eV.hom ≫ (DerivedCategory.singleFunctor C i).map q, ?_⟩
  intro hzero
  have hπ : (t.truncGEπ i).app U ≫
      (eV.hom ≫ (DerivedCategory.singleFunctor C i).map q) = 0 := by
    have hc : eU.inv ≫ ((t.truncGEπ i).app U ≫
        (eV.hom ≫ (DerivedCategory.singleFunctor C i).map q)) = eU.inv ≫ 0 := by
      simpa [p, Category.assoc] using hzero
    exact (cancel_epi eU.inv).mp hc
  have hV : eV.hom ≫ (DerivedCategory.singleFunctor C i).map q = 0 :=
    t.from_truncGE_obj_ext (by simpa using hπ)
  exact heV hV

/-- Given nonzero cohomology above `b` and a nonzero map out of each nonvanishing cohomology,
there is a degree above `b` with a nonzero map into `G` placed there. -/
private lemma exists_nonzero_hom_to_single_of_bounded_nonzero_homology
    {C : Type u} [Category C] [Abelian C] [HasDerivedCategory C]
    (K : DerivedCategory.Bounded C) (G : C) (b : ℤ)
    (hnot : ∃ i : ℤ, b < i ∧
      ¬ IsZero ((DerivedCategory.homologyFunctor C i).obj K.obj))
    (hMaps : ∀ i : ℤ, b < i →
      ¬ IsZero ((DerivedCategory.homologyFunctor C i).obj K.obj) →
      ∃ f : (DerivedCategory.homologyFunctor C i).obj K.obj ⟶ G, f ≠ 0) :
    ∃ i : ℤ, b < i ∧
      ∃ f : K.obj ⟶ (DerivedCategory.singleFunctor C i).obj G, f ≠ 0 := by
  obtain ⟨i, hbi, hni, htop⟩ := exists_top_nonzero_homology_above K b hnot
  have hLE : K.obj.IsLE i := by
    apply (DerivedCategory.isLE_iff K.obj i).2
    intro j hji
    by_contra hnj
    have hbj : b < j := lt_trans hbi hji
    have hle : j ≤ i := by
      exact le_of_not_gt (by intro hij; exact hnj (htop j hij))
    omega
  let : K.obj.IsLE i := hLE
  obtain ⟨f, hf⟩ := hMaps i hbi hni
  exact ⟨i, hbi,
    exists_nonzero_hom_to_single_of_nonzero_homology K.obj i inferInstance G f hf⟩

/-- The stalk of a coherent sheaf of modules is a finite module over the local ring. -/
private lemma finite_stalk_of_coherent (X : Scheme.{u}) (F : SheafOfModules.{u} X.ringCatSheaf)
    [F.IsCoherent] (x : X) :
    Module.Finite (X.presheaf.stalk x) (↑(OXModule.stalk F x)) := by
  let : F.IsFiniteType := SheafOfModules.IsCoherent.isFiniteType (M := F)
  exact SheafOfModules.finite_stalk X.sheaf F x

/-- A nonzero finite module over a local ring has a nonzero map to its residue field. -/
private lemma exists_nonzero_hom_to_residueField_of_finite
    (R : Type u) [CommRing R] [IsLocalRing R] (M : ModuleCat.{u} R)
    [Module.Finite R M] [Nontrivial M] :
    ∃ f : M ⟶ ModuleCat.of R (IsLocalRing.ResidueField R), f ≠ 0 := by
  have hTensor : ¬ Subsingleton (TensorProduct R (IsLocalRing.ResidueField R) (↑M)) := by
    intro h
    have hM : Subsingleton M := (IsLocalRing.subsingleton_tensorProduct (R := R)).mp h
    exact not_nontrivial_iff_subsingleton.mpr hM inferInstance
  have : Nontrivial (TensorProduct R (IsLocalRing.ResidueField R) (↑M)) :=
    not_subsingleton_iff_nontrivial.mp hTensor
  obtain ⟨z, hz⟩ := exists_ne (0 : TensorProduct R (IsLocalRing.ResidueField R) (↑M))
  let : Module.Free (IsLocalRing.ResidueField R)
      (TensorProduct R (IsLocalRing.ResidueField R) (↑M)) :=
    Module.Free.of_divisionRing _ _
  let : Module.Projective (IsLocalRing.ResidueField R)
      (TensorProduct R (IsLocalRing.ResidueField R) (↑M)) := Module.Projective.of_free
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual (IsLocalRing.ResidueField R)
      (TensorProduct R (IsLocalRing.ResidueField R) (↑M)), φ z ≠ 0 := by
    by_contra! h
    exact hz ((Module.forall_dual_apply_eq_zero_iff (IsLocalRing.ResidueField R) z).mp h)
  let μ : (↑M) →ₗ[R] IsLocalRing.ResidueField R :=
    (φ.restrictScalars R).comp (TensorProduct.mk R (IsLocalRing.ResidueField R) (↑M) 1)
  refine ⟨ModuleCat.ofHom μ, ?_⟩
  intro hμ
  apply hφ
  have hμ' : μ = 0 := ModuleCat.hom_ext_iff.mp hμ
  have hzero : ∀ y : TensorProduct R (IsLocalRing.ResidueField R) (↑M), φ y = 0 := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a m =>
        have hm := congrArg (fun f : (↑M) →ₗ[R] IsLocalRing.ResidueField R => f m) hμ'
        simp only [μ, LinearMap.coe_comp, Function.comp_apply, TensorProduct.mk_apply,
          LinearMap.coe_restrictScalars, LinearMap.zero_apply] at hm
        rw [← mul_one a, ← smul_eq_mul, ← smul_tmul', map_smul, hm, smul_zero]
    | add y y' hy hy' => rw [map_add, hy, hy', add_zero]
  exact hzero z

/-- A coherent sheaf with nonzero stalk at `x` has a nonzero map from that stalk to the residue
field at `x`. -/
private lemma exists_nonzero_hom_from_coherent_stalk_to_residueField
    (X : Scheme.{u}) [IsNoetherian X] (x : X) (F : SheafOfModules.{u} X.ringCatSheaf)
    [F.IsCoherent] (hF : ¬ IsZero (OXModule.stalk F x)) :
    ∃ f : OXModule.stalk F x ⟶
      ModuleCat.of (X.presheaf.stalk x) (IsLocalRing.ResidueField (X.presheaf.stalk x)),
      f ≠ 0 := by
  let M := OXModule.stalk F x
  have hns : ¬ Subsingleton (↑M) := by
    intro h
    exact hF (ModuleCat.isZero_iff_subsingleton.mpr h)
  let : Nontrivial (↑M) := not_subsingleton_iff_nontrivial.mp hns
  let : Module.Finite (X.presheaf.stalk x) (↑M) := finite_stalk_of_coherent X F x
  exact exists_nonzero_hom_to_residueField_of_finite (X.presheaf.stalk x) M

/-- For a bounded complex with coherent cohomology, stalk cohomology above `b`
vanishes exactly when all maps to the residue-field skyscraper in those degrees vanish. -/
@[stacks 0GWZ]
public theorem stalkHomology_isZero_iff_hom_residueFieldSkyscraper_subsingleton
    (X : Scheme.{u}) [IsNoetherian X] (x : X)
    [HasDerivedCategory (SheafOfModules.{u} X.ringCatSheaf)]
    (K : DerivedCategory.Bounded (SheafOfModules.{u} X.ringCatSheaf))
    (hK : ∀ i : ℤ,
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} X.ringCatSheaf) i).obj K.obj).IsCoherent)
    (b : ℤ) :
    (∀ i : ℤ, b < i →
      IsZero (OXModule.stalk
        ((DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) i).obj K.obj) x)) ↔
    (∀ i : ℤ, b < i →
      Subsingleton (K.obj ⟶
        (DerivedCategory.singleFunctor (SheafOfModules.{u} X.ringCatSheaf) i).obj
          (residueFieldSkyscraper X x))) := by
    classical
    have := HasDerivedCategory.standard (ModuleCat.{u} (X.presheaf.stalk x))
    let F : SheafOfModules.{u} X.ringCatSheaf ⥤ ModuleCat.{u} (X.presheaf.stalk x) :=
      stalkAt X x
    let S : ModuleCat.{u} (X.presheaf.stalk x) ⥤ SheafOfModules.{u} X.ringCatSheaf :=
      skyscraperModuleSheafFunctor X x
    let : F.Additive := stalkAt_additive X x
    let : PreservesFiniteLimits F := stalkAt_preservesFiniteLimits X x
    let : PreservesFiniteColimits F := stalkAt_preservesFiniteColimits X x
    let : S.Additive := skyscraperModuleSheafFunctor_additive X x
    let : PreservesFiniteLimits S := skyscraperModuleSheafFunctor_preservesFiniteLimits X x
    let : PreservesFiniteColimits S := skyscraperModuleSheafFunctor_preservesFiniteColimits X x
    let N := ModuleCat.of (X.presheaf.stalk x)
      (IsLocalRing.ResidueField (X.presheaf.stalk x))
    let L := F.mapDerivedCategory.obj K.obj
    let eH (i : ℤ) := (AlgebraicGeometry.derivedHomologyMapIso F K.obj i).symm
    let LB : DerivedCategory.Bounded (ModuleCat.{u} (X.presheaf.stalk x)) :=
      ⟨L, by
        obtain ⟨a, c, ha, hc⟩ := exists_bounds_of_bounded K
        have := ha
        have := hc
        have : L.IsGE a := (DerivedCategory.isGE_iff L a).2 (fun i hi =>
          (Functor.map_isZero F (DerivedCategory.isZero_of_isGE K.obj a i hi)).of_iso (eH i))
        have : L.IsLE c := (DerivedCategory.isLE_iff L c).2 (fun i hi =>
          (Functor.map_isZero F (DerivedCategory.isZero_of_isLE K.obj c i hi)).of_iso (eH i))
        exact ⟨⟨a, inferInstance⟩, ⟨c, inferInstance⟩⟩⟩
    let eS : S.obj N ≅ residueFieldSkyscraper X x :=
      (skyscraperSheafificationIso X x).symm.app N
    let adj := exactAdjunction_mapDerivedCategory (show F ⊣ S from moduleStalkAdjunction X x)
    let e (i : ℤ) :
        (L ⟶ (DerivedCategory.singleFunctor _ i).obj N) ≃
          (K.obj ⟶ (DerivedCategory.singleFunctor _ i).obj (residueFieldSkyscraper X x)) :=
      (adj.homEquiv K.obj ((DerivedCategory.singleFunctor _ i).obj N)).trans
        (Iso.homCongr (Iso.refl _)
          ((S.mapDerivedCategorySingleFunctor i).app N ≪≫
            (DerivedCategory.singleFunctor _ i).mapIso eS))
    constructor
    · intro h i hi
      have hL : ∀ j : ℤ, b < j →
          IsZero ((DerivedCategory.homologyFunctor _ j).obj L) :=
        fun j hj => (h j hj).of_iso (eH j)
      have := hom_subsingleton_of_homology_vanishes_above L N b i hi hL
      exact (e i).symm.injective.subsingleton
    · intro h i hi
      by_contra hni
      have hnot : ∃ j : ℤ, b < j ∧
          ¬ IsZero ((DerivedCategory.homologyFunctor _ j).obj LB.obj) :=
        ⟨i, hi, fun hz => hni (hz.of_iso (eH i).symm)⟩
      obtain ⟨j, hj, g, hg⟩ :=
        exists_nonzero_hom_to_single_of_bounded_nonzero_homology LB N b hnot (by
          intro j hj hnj
          have := hK j
          obtain ⟨f, hf⟩ := exists_nonzero_hom_from_coherent_stalk_to_residueField X x
            ((DerivedCategory.homologyFunctor
              (SheafOfModules.{u} X.ringCatSheaf) j).obj K.obj)
            (fun hz => hnj (hz.of_iso (eH j)))
          refine ⟨(eH j).hom ≫ f, ?_⟩
          intro hzero
          exact hf ((cancel_epi (eH j).hom).mp
            (hzero.trans Limits.comp_zero.symm)))
      have := h j hj
      have : Subsingleton (L ⟶ (DerivedCategory.singleFunctor _ j).obj N) :=
        (e j).injective.subsingleton
      exact hg (Subsingleton.elim _ _)

/-- A complex with no nonzero map to any shift of the residue-field skyscraper at `x` is zero on
an open neighbourhood of `x`: every cohomology sheaf has vanishing stalk at every point of that
neighbourhood. -/
@[stacks 0G03 "part (4), with the source's hypotheses `X` regular of finite type over a field \
and `K` in `D_perf(𝒪_X)` replaced by `X` Noetherian and `K` bounded with coherent cohomology, \
that is `K` in `D^b_Coh(𝒪_X)`.  The source's class of pairs sits inside this one, but the \
containment — a perfect object of `D(𝒪_X)` in the sense of \
`Stacks.Cohomology.PerfectComplexes.IsPerfect` is bounded with coherent cohomology, Tags 0BCJ \
and 08E8 — is not bridged in the library, so that is what is granted here.  `K` being zero near \
`x` is read as the vanishing of every cohomology stalk at every point of the neighbourhood"]
public theorem exists_mem_forall_stalkHomology_isZero_of_hom_residueFieldSkyscraper
    (X : Scheme.{u}) [IsNoetherian X] (x : X)
    [HasDerivedCategory (SheafOfModules.{u} X.ringCatSheaf)]
    (K : DerivedCategory.Bounded (SheafOfModules.{u} X.ringCatSheaf))
    (hK : ∀ i : ℤ,
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} X.ringCatSheaf) i).obj K.obj).IsCoherent)
    (h : ∀ i : ℤ,
      Subsingleton (K.obj ⟶
        (DerivedCategory.singleFunctor (SheafOfModules.{u} X.ringCatSheaf) i).obj
          (residueFieldSkyscraper X x))) :
    ∃ U : Opens X.carrier, x ∈ U ∧ ∀ y : X, y ∈ U → ∀ i : ℤ,
      IsZero (OXModule.stalk
        ((DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) i).obj K.obj) y) := by
  classical
  -- Orthogonality in every degree kills every cohomology stalk at `x`, by Tag 0GWZ.
  have hx : ∀ i : ℤ, IsZero (OXModule.stalk
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) i).obj K.obj) x) :=
    fun i => (stalkHomology_isZero_iff_hom_residueFieldSkyscraper_subsingleton X x K hK (i - 1)).mpr
      (fun j _ => h j) i (by omega)
  obtain ⟨a, b, ha, hb⟩ := exists_bounds_of_bounded K
  -- Outside the cohomological bounds the cohomology sheaf itself vanishes.
  have hout : ∀ i : ℤ, (i < a ∨ b < i) → ∀ y : X, IsZero (OXModule.stalk
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) i).obj K.obj) y) := by
    intro i hi y
    have := ha
    have := hb
    have hz : IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} X.ringCatSheaf) i).obj K.obj) := by
      rcases hi with hi | hi
      · exact DerivedCategory.isZero_of_isGE K.obj a i hi
      · exact DerivedCategory.isZero_of_isLE K.obj b i hi
    exact Functor.map_isZero (stalkAt X y) hz
  -- A coherent sheaf with vanishing stalk at `x` vanishes on a neighbourhood of `x`.
  have hstep : ∀ i : ℤ, ∃ U : Opens X.carrier, x ∈ U ∧ ∀ y : X, y ∈ U →
      IsZero (OXModule.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} X.ringCatSheaf) i).obj K.obj) y) := by
    intro i
    have hcoh := hK i
    have hft : ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} X.ringCatSheaf) i).obj K.obj).IsFiniteType :=
      SheafOfModules.IsCoherent.isFiniteType
    obtain ⟨U, hxU, hU⟩ :=
      Stacks.AlgebraicGeometry.Tag01Y3LocalIso.exists_forall_stalk_isZero_of_stalk_isZero
        (R := X.ringCatSheaf)
        ((DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) i).obj K.obj) x
        (AddCommGrpCat.isZero_iff_subsingleton.2
          (ModuleCat.isZero_iff_subsingleton.1 (hx i)))
    exact ⟨U, hxU, fun y hy => ModuleCat.isZero_iff_subsingleton.2
      (AddCommGrpCat.isZero_iff_subsingleton.1 (hU y hy))⟩
  choose V hxV hV using hstep
  refine ⟨⟨⋂ i ∈ (Finset.Icc a b : Finset ℤ), (V i : Set X.carrier),
    isOpen_biInter_finset fun i _ => (V i).isOpen⟩, Set.mem_biInter fun i _ => hxV i, ?_⟩
  intro y hy i
  by_cases hi : a ≤ i ∧ i ≤ b
  · exact hV i y (Set.mem_iInter₂.1 hy i (Finset.mem_Icc.2 hi))
  · exact hout i (by omega) y

end AlgebraicGeometry

end
