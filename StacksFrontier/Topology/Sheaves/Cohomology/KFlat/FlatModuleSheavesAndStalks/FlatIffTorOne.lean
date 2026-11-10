module


public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Topology.Sheaves.Skyscraper
public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import StacksFrontier.Topology.Sheaves.Skyscraper.Modules
public import StacksFrontier.CategoryTheory.Abelian.Projective.Horseshoe
public import Std.Tactic.BVDecide.Normalize.Prop
public import StacksFrontier.CategoryTheory.Abelian.Projective.Horseshoe
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.FlatModuleSheavesAndStalks.TorOneAndSkyscraper

/-!
# Flatness of `O_X`-modules is stalkwise, and `Tor_1` measures flatness (Tags 05NE, 08BQ)

This file makes the skyscraper realization of `FlatModuleSheavesAndStalks.TorOneAndSkyscraper`
functorial, so that an injection of `O_{X,x}`-modules is realized as the stalk of a
monomorphism of `O_X`-modules, and proves `OXModule.flat_iff_flat_stalk` (Tag 05NE: flatness
is equivalent to stalkwise flatness) and the stalk-level reading
`OXModule.flat_iff_tor1_eq_zero` of Tag 08BQ.  It ends with an `eqToHom`-free API for the
sections of the skyscraper module, including its pushforward along a morphism of ringed spaces
(`OXModule.skyscraperPOMPushforwardIso`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TopCat

universe u

namespace OXModule

variable {X : AlgebraicGeometry.RingedSpace.{u, u}}

attribute [local instance] sectionModule sectionPresheafModule stalkModule

/-! ### Functoriality of the skyscraper realization (Tag 05NE, ⇒ direction)

To test flatness of `F.stalk x` against an *arbitrary* injective `O_{X,x}`-linear map
`g : N' →ₗ N`, we realize `g` itself as the stalk of a monomorphism of `O_X`-modules.
The skyscraper construction `skyscraperPOM x (-)` is functorial in the module, and its
stalk at `x` is canonically `N` (`sheafify_skyscraperPOM_stalk_iso`); the induced
morphism on stalks is, under these identifications, exactly `g`. -/

/-- The component at `U` of the skyscraper morphism induced by `g : N' ⟶ N`:
on opens containing `x` it is `g` (restricted along the germ), elsewhere it is `0`. -/
noncomputable def skyscraperMapHomApp (x : X.carrier)
    {N' N : ModuleCat.{u} (X.presheaf.stalk x)} (g : N' ⟶ N)
    (U : (TopologicalSpace.Opens X.carrier)ᵒᵖ) :
    skyscraperObj x N' U ⟶ skyscraperObj x N U := by
  classical
  by_cases h : x ∈ U.unop
  · refine eqToHom (by rw [skyscraperObj, dite_eq_left h]) ≫
      (ModuleCat.restrictScalars (X.presheaf.germ U.unop x h).hom).map g ≫
      eqToHom ?_
    rw [skyscraperObj, dite_eq_left h]
  · exact 0

/-- The skyscraper morphism of presheaves-of-modules induced by `g : N' ⟶ N`. -/
noncomputable def skyscraperPOMMap (x : X.carrier)
    {N' N : ModuleCat.{u} (X.presheaf.stalk x)} (g : N' ⟶ N) :
    skyscraperPOM x N' ⟶ skyscraperPOM x N where
  app U := skyscraperMapHomApp x g U
  naturality := by
    classical
    intro U W f
    change skyscraperMap x N' f ≫
        (ModuleCat.restrictScalars
          (RingCat.Hom.hom ((X.presheaf ⋙ forget₂ CommRingCat RingCat).map f))).map
          (skyscraperMapHomApp x g W)
      = skyscraperMapHomApp x g U ≫ skyscraperMap x N f
    by_cases hW : x ∈ W.unop
    · have hU : x ∈ U.unop := (leOfHom f.unop) hW
      rw [skyscraperMap, dite_eq_left hW, skyscraperMapHomApp, dite_eq_left hW,
        skyscraperMapHomApp, dite_eq_left hU, skyscraperMap, dite_eq_left hW]
      have hnat := (ModuleCat.restrictScalarsComp' ((X.presheaf.map f).hom)
        (X.presheaf.germ W.unop x hW).hom (X.presheaf.germ U.unop x hU).hom
        (structure_germ_comp x f hW)).hom.naturality g
      simp only [Functor.comp_map, ModuleCat.restrictScalarsComp'_hom_app,
        restrictScalarsComp'App_hom_eqToHom] at hnat
      simp only [Functor.map_comp, ModuleCat.restrictScalarsComp'_hom_app,
        restrictScalarsComp'App_hom_eqToHom, eqToHom_map, eqToHom_trans,
        Category.assoc, eqToHom_trans_assoc]
      rw [eq_comm, eqToHom_comp_iff] at hnat
      rw [eqToHom_comp_iff, comp_eqToHom_iff]
      simp only [eqToHom_trans, eqToHom_trans_assoc, Category.assoc]
      exact hnat
    · rw [skyscraperMapHomApp, dite_eq_right hW]
      have hsub : Subsingleton
          ((ModuleCat.restrictScalars
            (RingCat.Hom.hom ((X.presheaf ⋙ forget₂ CommRingCat RingCat).map f))).obj
              (skyscraperObj x N W)) := by
        have : (skyscraperObj x N W) = ModuleCat.of _ PUnit.{u+1} := by
          rw [skyscraperObj, dite_eq_right hW]
        rw [this]; exact inferInstanceAs (Subsingleton PUnit.{u+1})
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro y
      exact Subsingleton.elim _ _

/-- On opens containing `x`, the underlying `AddCommGrp` app of `skyscraperPOMMap x g`
is, under the canonical `= AddCommGrpCat.of N` identifications, just `g`. -/
theorem skyscraperPOMMap_presheaf_app_eq (x : X.carrier)
    {N' N : ModuleCat.{u} (X.presheaf.stalk x)} (g : N' ⟶ N)
    (U : (TopologicalSpace.Opens X.carrier)ᵒᵖ) (hx : x ∈ U.unop)
    (s : (skyscraperPOM x N').presheaf.obj U) :
    (ConcreteCategory.hom (eqToHom (skyscraperPOM_presheaf_obj_eq x N U hx)))
        ((ConcreteCategory.hom (((PresheafOfModules.toPresheaf _).map (skyscraperPOMMap x g)).app
            U)) s)
      = (ConcreteCategory.hom g)
          ((ConcreteCategory.hom (eqToHom (skyscraperPOM_presheaf_obj_eq x N' U hx))) s) := by
  classical
  let forgetOpen := forget₂ (ModuleCat ↑((X.presheaf ⋙ forget₂ CommRingCat RingCat).obj U))
    AddCommGrpCat
  let restrictedMap := (ModuleCat.restrictScalars (X.presheaf.germ U.unop x hx).hom).map g
  have sourceEquality : skyscraperObj x N' U =
      (ModuleCat.restrictScalars (X.presheaf.germ U.unop x hx).hom).obj N' := by
    rw [skyscraperObj, dite_eq_left hx]
  have targetEquality : skyscraperObj x N U =
      (ModuleCat.restrictScalars (X.presheaf.germ U.unop x hx).hom).obj N := by
    rw [skyscraperObj, dite_eq_left hx]
  let sourceIso := eqToIso (skyscraperPOM_presheaf_obj_eq x N' U hx)
  let targetIso := eqToIso (skyscraperPOM_presheaf_obj_eq x N U hx)
  let middle := (forget₂ (ModuleCat ↑(X.presheaf.stalk x)) AddCommGrpCat).map g
  have appEquality : skyscraperMapHomApp x g U =
      eqToHom sourceEquality ≫ restrictedMap ≫ eqToHom targetEquality.symm :=
    dite_eq_left hx
  have sourceCast : forgetOpen.map (eqToHom sourceEquality) = sourceIso.hom :=
    eqToHom_map forgetOpen sourceEquality
  have targetCast : forgetOpen.map (eqToHom targetEquality.symm) = targetIso.inv :=
    eqToHom_map forgetOpen targetEquality.symm
  have middleMap : forgetOpen.map restrictedMap = middle := rfl
  have transported : ((PresheafOfModules.toPresheaf _).map (skyscraperPOMMap x g)).app U =
      sourceIso.hom ≫ middle ≫ targetIso.inv :=
    (congrArg forgetOpen.map appEquality).trans
      ((forgetOpen.map_comp (eqToHom sourceEquality)
        (restrictedMap ≫ eqToHom targetEquality.symm)).trans
          ((congrArg (fun morphism => forgetOpen.map (eqToHom sourceEquality) ≫ morphism)
            (forgetOpen.map_comp restrictedMap (eqToHom targetEquality.symm))).trans
              (congrArg₂ (· ≫ ·) sourceCast (congrArg₂ (· ≫ ·) middleMap targetCast))))
  have conjugated : ((PresheafOfModules.toPresheaf _).map (skyscraperPOMMap x g)).app U ≫
      targetIso.hom = sourceIso.hom ≫ middle :=
    (congrArg (fun morphism => morphism ≫ targetIso.hom) transported).trans
      ((Category.assoc sourceIso.hom (middle ≫ targetIso.inv) targetIso.hom).trans
        (congrArg (fun morphism => sourceIso.hom ≫ morphism)
          ((Category.assoc middle targetIso.inv targetIso.hom).trans
            ((congrArg (fun morphism => middle ≫ morphism) targetIso.inv_hom_id).trans
              (Category.comp_id middle)))))
  exact (ConcreteCategory.comp_apply
    (((PresheafOfModules.toPresheaf _).map (skyscraperPOMMap x g)).app U) targetIso.hom
      s).symm.trans
      ((ConcreteCategory.congr_hom conjugated s).trans
        (ConcreteCategory.comp_apply sourceIso.hom middle s))

/-- The realization iso `sheafify_skyscraperPOM_stalk_iso` sends the stalk class of a
germ (transported through the sheafification-unit stalk iso `sheafifyStalkFwd`) to the
corresponding value in `N`, under the canonical identification. -/
theorem sheafify_skyscraperPOM_stalk_iso_germ (x : X.carrier)
    (N : ModuleCat.{u} (X.presheaf.stalk x))
    (U : (TopologicalSpace.Opens X.carrier)ᵒᵖ) (hx : x ∈ U.unop)
    (s : (skyscraperPOM x N).presheaf.obj U) :
    (ConcreteCategory.hom (sheafify_skyscraperPOM_stalk_iso x N).hom)
        (sheafifyStalkFwd x (skyscraperPOM x N)
          ((ConcreteCategory.hom (TopCat.Presheaf.germ (skyscraperPOM x N).presheaf U.unop x hx))
              s))
      = (ConcreteCategory.hom (eqToHom (skyscraperPOM_presheaf_obj_eq x N U hx))) s := by
  let germValue := (TopCat.Presheaf.germ (skyscraperPOM x N).presheaf U.unop x hx).hom s
  have cancelUnit := (sheafifyStalkLinearEquiv x (skyscraperPOM x N)).symm_apply_apply germValue
  exact (ConcreteCategory.comp_apply (sheafify_skyscraperPOM_stalkIso_O1 x N).hom
    (sheafify_skyscraperPOM_stalkIso_skyscraper x N).hom
    (sheafifyStalkFwd x (skyscraperPOM x N) germValue)).trans
      ((congrArg (ConcreteCategory.hom (sheafify_skyscraperPOM_stalkIso_skyscraper x N).hom)
        cancelUnit).trans (sheafify_skyscraperPOM_stalkIso_skyscraper_addEquiv_germ x N U hx s))

/-- Every component of the underlying `AddCommGrp` presheaf morphism of
`skyscraperPOMMap x g` is injective when `g` is injective: on opens containing `x`
it is `g` (sandwiched by the bijective identifications), elsewhere a map of
subsingletons. -/
theorem skyscraperPOMMap_presheaf_app_injective (x : X.carrier)
    {N' N : ModuleCat.{u} (X.presheaf.stalk x)} (g : N' ⟶ N)
    (hg : Function.Injective (ConcreteCategory.hom g))
    (U : (TopologicalSpace.Opens X.carrier)ᵒᵖ) :
    Function.Injective
      (ConcreteCategory.hom
        (((PresheafOfModules.toPresheaf _).map (skyscraperPOMMap x g)).app U)) := by
  classical
  by_cases hx : x ∈ U.unop
  · intro a b hab
    -- apply `eqToHom (obj_eq N)` to both sides, then use the `= g` characterization
    have ha := skyscraperPOMMap_presheaf_app_eq x g U hx a
    have hb := skyscraperPOMMap_presheaf_app_eq x g U hx b
    rw [hab] at ha
    rw [ha] at hb
    -- hb : g (eqToHom_N' a) = g (eqToHom_N' b)
    have hinj := hg hb
    -- eqToHom is bijective, hence injective, so a = b
    exact (ConcreteCategory.bijective_of_isIso
      (eqToHom (skyscraperPOM_presheaf_obj_eq x N' U hx))).injective hinj
  · -- source is a subsingleton (PUnit), so any map is injective
    have hpu : ((skyscraperPOM x N').presheaf.obj U : Type u) = (PUnit.{u+1} : Type u) := by
      change ((forget₂ (ModuleCat _) AddCommGrpCat).obj (skyscraperObj x N' U) : Type u) = _
      rw [skyscraperObj, dite_eq_right hx]; rfl
    intro a b _
    have hcast : (cast hpu a) = (cast hpu b) := Subsingleton.elim _ _
    exact (Equiv.cast hpu).injective hcast

/-- Every element of a stalk of a sheafification is the image under `sheafifyStalkFwd` of the
germ of a section of the presheaf. -/
private theorem exists_germ_sheafifyStalkFwd_eq (y : X.carrier)
    (P : PresheafOfModules.{u} ((ringSheaf X).obj))
    (a : ↑(TopCat.Presheaf.stalk (sheafify.obj P).val.presheaf y)) :
    ∃ (U : TopologicalSpace.Opens X.carrier) (hU : y ∈ U) (s : P.presheaf.obj (Opposite.op U)),
      a = sheafifyStalkFwd y P
        ((ConcreteCategory.hom (TopCat.Presheaf.germ P.presheaf U y hU)) s) := by
  obtain ⟨U, hU, s, hs⟩ := TopCat.Presheaf.exists_germ_eq (x := y) P.presheaf
    ((sheafifyStalkLinearEquiv y P).symm a)
  exact ⟨U, hU, s, by rw [hs]; exact ((sheafifyStalkLinearEquiv y P).apply_symm_apply a).symm⟩

/-- **Realization of an injection as a sheaf monomorphism on stalks (Tag 05NE ⇒ core).**
Given an injective `O_{X,x}`-linear map `g : N' →ₗ N`, there exist `O_X`-modules `M`, `M'`,
a monomorphism `φ : M ⟶ M'`, and `O_{X,x}`-linear isomorphisms `α : M.stalk x ≅ N'`,
`β : M'.stalk x ≅ N`, such that the stalk map of `φ` is `g` up to `α, β`, i.e. the square
`β ∘ (stalkLinearMap M M' φ x) = g ∘ α` commutes.

The witnesses are `M = sheafify (skyscraperPOM x N')`, `M' = sheafify (skyscraperPOM x N)`,
`φ = sheafify.map (skyscraperPOMMap x g)`; `α, β` are the realization isos
`sheafify_skyscraperPOM_stalk_iso`; the commuting square is the naturality of that
realization iso in the module variable (and `Mono φ` is detected stalkwise). -/
theorem exists_stalk_realized_mono (x : X.carrier)
    {N' N : ModuleCat.{u} (X.presheaf.stalk x)} (g : N' ⟶ N)
    (hg : Function.Injective (ConcreteCategory.hom g)) :
    ∃ (M M' : OXModule X) (φ : M ⟶ M')
      (α : stalk M x ≅ N') (β : stalk M' x ≅ N),
      Mono φ ∧
      ∀ z : stalk M x,
        (ConcreteCategory.hom β.hom) (stalkMapAdd M M' φ x z)
          = (ConcreteCategory.hom g) ((ConcreteCategory.hom α.hom) z) := by
  classical
  refine ⟨sheafify.obj (skyscraperPOM x N'), sheafify.obj (skyscraperPOM x N),
    sheafify.map (skyscraperPOMMap x g),
    sheafify_skyscraperPOM_stalk_iso x N', sheafify_skyscraperPOM_stalk_iso x N, ?_, ?_⟩
  · -- Mono φ
    apply mono_of_stalkMapAdd_injective
    intro y
    -- the underlying presheaf morphism of `skyscraperPOMMap x g` is locally injective
    have hLI : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X.carrier)
        ((PresheafOfModules.toPresheaf _).map (skyscraperPOMMap x g)) :=
      Presheaf.isLocallyInjective_of_injective _ _
        (skyscraperPOMMap_presheaf_app_injective x g hg)
    -- hence the presheaf-level stalk map at `y` is injective
    have hpsh : Function.Injective ((TopCat.Presheaf.stalkFunctor _ y).map
        ((PresheafOfModules.toPresheaf _).map (skyscraperPOMMap x g))) :=
      stalkMap_injective_of_isLocallyInjective
        ((PresheafOfModules.toPresheaf _).map (skyscraperPOMMap x g)) y
    -- transport injectivity across the bijective `sheafifyStalkFwd` on both sides
    intro a b hab
    obtain ⟨Ua, hxUa, sa, rfl⟩ := exists_germ_sheafifyStalkFwd_eq y (skyscraperPOM x N') a
    obtain ⟨Ub, hxUb, sb, rfl⟩ := exists_germ_sheafifyStalkFwd_eq y (skyscraperPOM x N') b
    rw [sheafifyStalkFwd_naturality y (skyscraperPOMMap x g) Ua hxUa sa,
      sheafifyStalkFwd_naturality y (skyscraperPOMMap x g) Ub hxUb sb] at hab
    -- strip the (injective) outer `sheafifyStalkFwd y P`
    have hgerm := hpsh ((sheafifyStalkLinearEquiv y (skyscraperPOM x N)).injective hab)
    rw [hgerm]
  · -- naturality square
    intro z
    -- write `z` as the sheafify-fwd image of a germ in the skyscraper presheaf stalk
    obtain ⟨U, hxU, s, rfl⟩ := exists_germ_sheafifyStalkFwd_eq x (skyscraperPOM x N') z
    -- RHS: α.hom sends the fwd-germ to the value of `s` in `N'`
    rw [sheafify_skyscraperPOM_stalk_iso_germ x N' (Opposite.op U) hxU s]
    -- LHS: push the stalk map through `sheafifyStalkFwd` naturality
    rw [sheafifyStalkFwd_naturality x (skyscraperPOMMap x g) U hxU s]
    have hgerm := TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU
      ((PresheafOfModules.toPresheaf _).map (skyscraperPOMMap x g)) s
    exact (congrArg (fun germ =>
      (ConcreteCategory.hom (sheafify_skyscraperPOM_stalk_iso x N).hom)
        (sheafifyStalkFwd x (skyscraperPOM x N) germ)) hgerm).trans
      ((sheafify_skyscraperPOM_stalk_iso_germ x N (Opposite.op U) hxU
        ((ConcreteCategory.hom (((PresheafOfModules.toPresheaf _).map
          (skyscraperPOMMap x g)).app (Opposite.op U))) s)).trans
        (skyscraperPOMMap_presheaf_app_eq x g (Opposite.op U) hxU s))

/-- **Skyscraper realization (assembled).**
Takes `G := sheafify (skyscraperPOM x N)` and the stalk iso
`sheafify_skyscraperPOM_stalk_iso`.  The three ingredients are
`skyscraperMap_id` (`:2300`), `skyscraperMap_comp` (`:2340`) — the coherence of
the skyscraper on morphisms — and `sheafify_skyscraperPOM_stalk_iso` (`:2623`),
the stalk computation; all three are proved above. -/
theorem exists_oxModule_stalk_iso_skyscraper
    (x : X.carrier) (N : ModuleCat.{u} (X.presheaf.stalk x)) :
    ∃ G : OXModule X, Nonempty (G.stalk x ≅ N) :=
  ⟨sheafify.obj (skyscraperPOM x N), ⟨sheafify_skyscraperPOM_stalk_iso x N⟩⟩

alias exists_oxModule_stalk_iso := OXModule.exists_oxModule_stalk_iso_skyscraper

/-- **Leaf (Tag 05NE, ⇒ stalk-local core).**  If `F` is flat as an `O_X`-module then
every stalk `F_x` is a flat `O_{X,x}`-module.  Given an injection `g : N' ↪ N` of
`O_{X,x}`-modules, `exists_stalk_realized_mono` realizes it as the stalk map of a sheaf
monomorphism `φ`; `(tensorBy F).map φ` is a mono by flatness, so its stalk map is
injective; the transport helper_08bq `rTensor_stalkLinearMap_injective_of_tensorBy_stalk_injective`
turns this into injectivity of `rTensor F_x (φ_x)`, and the realization square
transports that to injectivity of `rTensor F_x g`. -/
@[sga "4 V 1.6" "assertion 1",
  sga "4 V 1.6.2" "special case",
  sga "4 V 1.7.1" "special case",
  sga "6 I 5.6.2" "special case",
  sga "6 III 3.3" "(i)⇒(ii), special case"]
theorem flat_stalk_of_flat (F : OXModule X) (hF : F.Flat) (x : X.carrier) :
    Module.Flat (X.presheaf.stalk x) (stalk F x) := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro N' N _ _ _ _ g hg
  -- Realize `g` as the stalk map of a sheaf monomorphism `φ : M ⟶ M'`.
  obtain ⟨M, M', φ, α, β, hmono, hsq⟩ :=
    exists_stalk_realized_mono x (ModuleCat.ofHom g) hg
  -- `(tensorBy F).map φ` is a monomorphism by flatness of `F`.
  have : Mono φ := hmono
  have : (tensorBy F).PreservesMonomorphisms := hF
  have : Mono ((tensorBy F).map φ) := (tensorBy F).map_mono φ
  -- hence its stalk map at `x` is injective
  have hS : Function.Injective
      (stalkMapAdd ((tensorBy F).obj M) ((tensorBy F).obj M') ((tensorBy F).map φ) x) :=
    stalkMapAdd_injective_of_mono ((tensorBy F).obj M) ((tensorBy F).obj M') ((tensorBy F).map φ) x
  -- transport helper_08bq: `rTensor F_x (φ_x)` is injective
  have hφx : Function.Injective
      (LinearMap.rTensor (F.stalk x) (stalkLinearMap M M' φ x)) :=
    rTensor_stalkLinearMap_injective_of_tensorBy_stalk_injective F M M' φ x hS
  -- The realization square: `β.hom ∘ φ_x = g ∘ α.hom` as O_{X,x}-linear maps.
  -- Equivalently `φ_x = β.symm.hom ∘ g ∘ α.hom`.
  -- We deduce injectivity of `rTensor F_x g`.
  set sx : stalk M x →ₗ[X.presheaf.stalk x] stalk M' x := stalkLinearMap M M' φ x with hsx
  -- `rTensor` of an isomorphism is bijective.
  have hbij : ∀ {A B : ModuleCat.{u} (X.presheaf.stalk x)} (e : A ≅ B),
      Function.Bijective (LinearMap.rTensor (F.stalk x) (ModuleCat.Hom.hom e.hom)) :=
    fun e => (e.toLinearEquiv.rTensor (F.stalk x)).bijective
  -- From hsq : β.hom (sx z) = g (α.hom z): `β.hom ∘ sx = g ∘ α.hom` as linear maps.
  have hcomp : (ModuleCat.Hom.hom β.hom).comp sx
      = (g).comp (ModuleCat.Hom.hom α.hom) := LinearMap.ext hsq
  -- Apply rTensor (which is a functor): rTensor (β.hom ∘ sx) = rTensor (g ∘ α.hom).
  have hrt : (LinearMap.rTensor (F.stalk x) (ModuleCat.Hom.hom β.hom)).comp
        (LinearMap.rTensor (F.stalk x) sx)
      = (LinearMap.rTensor (F.stalk x) g).comp
        (LinearMap.rTensor (F.stalk x) (ModuleCat.Hom.hom α.hom)) := by
    rw [← LinearMap.rTensor_comp, ← LinearMap.rTensor_comp, hcomp]
  -- The LHS is injective, so `rTensor g ∘ rTensor α.hom` is; cancel the bijection `rTensor α.hom`.
  have h := (hbij β).1.comp hφx
  rw [← LinearMap.coe_comp, hrt, LinearMap.coe_comp] at h
  exact (Function.Injective.of_comp_iff' _ (hbij α)).1 h

/-- **Correctness for Definition 2 (Tag 05NE).**
Sheaf-level flatness (Definition 2, exactness of `- ⊗_{O_X} F`) is equivalent
to stalk-wise flatness.  The categorical heart — that monomorphisms of
`O_X`-modules are detected on stalks — is proven with no open goals above
(`mono_of_stalkMapAdd_injective` / `stalkMapAdd_injective_of_mono`). -/
@[sga "4 V 1.6" "special case",
  sga "6 I 5.6.2" "special case",
  sga "6 III 3.3" "(i)⇔(ii), special case",
  sga "6 III 5.2" "(ii), special case"]
theorem flat_iff_flat_stalk (F : OXModule X) : F.Flat ↔ F.FlatStalkwise := by
  constructor
  · -- (⇒) sheaf-flat ⇒ stalkwise-flat
    intro hF x
    exact flat_stalk_of_flat F hF x
  · -- (⇐) stalkwise-flat ⇒ sheaf-flat
    intro hF
    refine ⟨fun {M N} f => ?_⟩
    intro hmono
    apply mono_of_stalkMapAdd_injective
    intro x
    exact tensorBy_stalk_injective_of_flat F M N f
      (fun x => stalkMapAdd_injective_of_mono M N f x) hF x

/-- **Stalk-wise flatness ↔ stalk-wise `Tor₁` vanishing for all `G`.**
Combining the per-ring heart with the realization lemma: `F` is stalk-wise flat
iff `Tor₁^{O_X}(F,G)` vanishes (stalk-wise) for every `O_X`-module `G`.

*Argument.*
`(⇒)` Assume each `F_x` is flat.  Given any `G` and any `x`, `module_flat_iff_tor1`
applied to `M := F_x` and `N := G_x` gives `Tor₁(F_x, G_x) = 0`, i.e.
`Tor1IsZero F G`.
`(⇐)` Assume `∀ G, Tor1IsZero F G`.  Fix `x`; to show `F_x` flat use
`module_flat_iff_tor1`, so it suffices to show `Tor₁(F_x, N) = 0` for every
`O_{X,x}`-module `N`.  By `exists_oxModule_stalk_iso` choose `G` with
`G_x ≅ N`; the hypothesis at this `G` and this `x` gives `Tor₁(F_x, G_x) = 0`,
and transporting along the iso `G_x ≅ N` (functoriality of `Tor` in the second
variable preserves `IsZero` under isomorphism) yields `Tor₁(F_x, N) = 0`. -/
theorem flatStalkwise_iff_forall_tor1 (F : OXModule X) :
    F.FlatStalkwise ↔ ∀ G : OXModule X, F.Tor1IsZero G := by
  constructor
  · -- (⇒) flat stalks ⇒ all Tor₁ vanish
    intro hF G x
    -- `hF x : Module.Flat (O_{X,x}) (F.stalk x)`; apply the per-ring criterion at N = G.stalk x
    exact (module_flat_iff_tor1 _ (F.stalk x)).1 (hF x) (G.stalk x)
  · -- (⇐) all Tor₁ vanish ⇒ flat stalks (uses skyscraper realization)
    intro hTor x
    rw [module_flat_iff_tor1]
    intro N
    obtain ⟨G, ⟨e⟩⟩ := exists_oxModule_stalk_iso x N
    -- `hTor G x : IsZero (Tor₁ (F.stalk x) (G.stalk x))`; transport along `e : G.stalk x ≅ N`
    have h0 : IsZero (((Tor (ModuleCat.{u} (X.presheaf.stalk x)) 1).obj (F.stalk x)).obj (G.stalk
        x)) :=
      hTor G x
    -- transport `IsZero` along the iso induced by `e` in the second Tor argument
    exact h0.of_iso (((Tor (ModuleCat.{u} (X.presheaf.stalk x)) 1).obj (F.stalk x)).mapIso e.symm)

-- Main Statement(s)

/-- **Theorem (Stacks Tag 08BQ — "Tor measures the deviation of flatness").**
Let `(X, O_X)` be a ringed space and `F` an `O_X`-module.  Then `F` is flat
(Definition 2: the genuine tensor endofunctor `- ⊗_{O_X} F` is exact) if and
only if `Tor_1^{O_X}(F, G)` is the zero `O_X`-module for every `O_X`-module
`G`.

The tensor product (Definition 1) is formalized directly as the sheafification
of the presheaf tensor product, and `Flat` is the genuine sheaf-level exactness
of this tensor, so the left-hand side is the source's own notion (Tag 05ND).

The right-hand side is the **stalk-level** reading: `Tor1IsZero F G` says that
the classical module-theoretic `Tor_1^{O_{X,x}}(F_x, G_x)` vanishes at every
`x`.  It is not the expression `Stacks.Cohomology.tor X 1 F G` (Tag 08BP), the
genuine `H^{-1}(F ⊗^{L}_{O_X} G)`, which is what the tag's clause (2) is about;
and `tor1IsZero_iff_stalk` is `Iff.rfl`, so it supplies no part of the
comparison.

The two readings are nevertheless **the same statement**, and that is now a
theorem rather than a gap: `Stacks.Cohomology.flat_iff_forall_isZero_tor` in
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedTensor/TorFlatness.lean` states
Tag 08BQ with clause (2) in the source's own terms, and
`Stacks.SheafOfModules.DerivedTensorStalk.isZero_derivedTensorHomology_iff_forall_isZero_tor`
there is the identification itself: the sheaf `Tor_p` of Tag 08BP vanishes
exactly when the stalkwise module-theoretic `Tor_p` vanishes at every point.
Its four ingredients are
`AlgebraicGeometry.SheafOfModules.isZero_iff_forall_isZero_stalkFunctor_obj`
(vanishing is stalkwise, Tag 01AG),
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso` (the exact stalk functor
commutes with `H^{-1}`),
`Stacks.SheafOfModules.DerivedTensorStalk.derivedTensorStalkIso` (the derived
form of Tag 01CB) — all three of which already existed — and
`Stacks.DerivedTensor.homologyIsoTor`
(`StacksFrontier/Homology/Tor/DerivedTensorTor.lean`), the identification of
`H^{-p}` of a derived tensor product of two modules over a commutative ring
with their `Tor_p`, which is the one that had to be supplied.

So this declaration is the stalk-level half of the tag, kept because the rest of
this file is written in the stalkwise vocabulary; the tag's own statement is the
one in `StacksFrontier/Topology/Sheaves/Cohomology/DerivedTensor/TorFlatness.lean`.

*Proof.*  By `flat_iff_flat_stalk` (Tag 05NE) sheaf flatness is equivalent to
stalk-wise flatness `F.FlatStalkwise`, and by `flatStalkwise_iff_forall_tor1`
the latter is equivalent to the vanishing of all stalk-wise `Tor₁`. -/
@[stacks 08BQ "(1) ⟺ (2) with clause (2) read stalkwise: Tor_1 here is the module-theoretic
Tor_1^{O_{X,x}}(F_x, G_x) at every point, not the sheaf Tor_1 of Tag 08BP. The tag's clause (2)
in the source's own terms — the vanishing of Stacks.Cohomology.tor X 1 F G — is
Stacks.Cohomology.flat_iff_forall_isZero_tor in
StacksFrontier/Topology/Sheaves/Cohomology/DerivedTensor/TorFlatness.lean, and the two readings are
identified there by isZero_derivedTensorHomology_iff_forall_isZero_tor.",
  sga "6 I 5.1.1" "special case"]
theorem flat_iff_tor1_eq_zero (F : OXModule X) :
    F.Flat ↔ ∀ G : OXModule X, F.Tor1IsZero G := by
  rw [flat_iff_flat_stalk, flatStalkwise_iff_forall_tor1]

end OXModule

/-! ### An `eqToHom`-free API for the sections of the skyscraper module

The skyscraper presheaf of modules `skyscraperPOM` above is built sectionwise from a `dite`
(`skyscraperObj`), so comparisons with Mathlib's `skyscraperPresheaf`, and with the pushforward
along a morphism of ringed spaces, do not go through at `implicit` transparency.  This section
supplies the named comparisons that let consumers avoid those definitional unfoldings:
`skyscraperPOMPresheafIso` for the underlying presheaf of abelian groups,
`skyscraperPOM_presheaf_smul` for the scalar action on sections at the module structure that
`PresheafOfModules` puts on them, and `skyscraperPOMPushforwardIso` for the pushforward along a
morphism of ringed spaces.  All of the proofs below were developed and checked in a file with
no elaboration options set, so that they remain usable from such a file.
-/

section SkyscraperSections

open TopologicalSpace Opposite AlgebraicGeometry

universe v w

namespace ModuleCat

/-- Restriction of scalars does not change the underlying additive group. -/
theorem forget₂_restrictScalars_obj {R S : Type u} [Ring R] [Ring S] (φ : R →+* S)
    (N : ModuleCat.{v} S) :
    (forget₂ (ModuleCat R) AddCommGrpCat).obj ((ModuleCat.restrictScalars φ).obj N) =
      (forget₂ (ModuleCat S) AddCommGrpCat).obj N := rfl

/-- Transporting along an equality of `ModuleCat` objects, at the level of underlying types,
is semilinear for the identity: it commutes with the scalar action. -/
theorem cast_smul_of_eq {R : Type u} [Ring R] {M₁ M₂ : ModuleCat.{u} R} (h : M₁ = M₂)
    (hT : (↑M₁ : Type u) = ↑M₂) (r : R) (m : (↑M₁ : Type u)) :
    cast hT (r • m) = r • cast hT m := by
  subst h
  simp

/-- Restriction of scalars does not change the underlying additive group. -/
theorem addCommGrpCat_of_restrictScalars_obj {R S : Type u} [Ring R] [Ring S] (φ : R →+* S)
    (N : ModuleCat.{v} S) :
    AddCommGrpCat.of ↑((ModuleCat.restrictScalars φ).obj N) = AddCommGrpCat.of ↑N := rfl

end ModuleCat

namespace PresheafOfModules

/-- The underlying presheaf of abelian groups of a pushforward of a presheaf of modules is
the precomposition of the underlying presheaf of abelian groups. -/
theorem pushforward_presheaf {C : Type u} [Category.{v} C] {D : Type w} [Category.{v} D]
    {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R)
    (M : PresheafOfModules.{u} R) :
    ((pushforward φ).obj M).presheaf = F.op ⋙ M.presheaf := rfl

end PresheafOfModules

section SkyscraperPushforward

variable {C : Type v} [Category.{w} C] [HasTerminal C]

/-- Pushing a skyscraper presheaf forward along a continuous map is the skyscraper presheaf
at the image point. -/
theorem skyscraperPresheaf_pushforward_eq {X Y : TopCat.{u}} (g : X ⟶ Y) (x : X) (A : C)
    [hd : ∀ U : Opens X, Decidable (x ∈ U)]
    [∀ V : Opens Y, Decidable ((ConcreteCategory.hom g) x ∈ V)] :
    (Opens.map g).op ⋙ skyscraperPresheaf x A =
      skyscraperPresheaf ((ConcreteCategory.hom g) x) A := by
  convert_to (Opens.map g).op ⋙ skyscraperPresheaf x A =
    @skyscraperPresheaf Y ((ConcreteCategory.hom g) x)
      (fun V => hd ((Opens.map g).obj V)) C _ _ A
  · congr
  · rfl

end SkyscraperPushforward

namespace OXModule

variable {X : AlgebraicGeometry.RingedSpace.{u, u}}

/-- On opens not containing `x`, the sections of the skyscraper presheaf of modules form a
terminal object of `AddCommGrpCat`. -/
noncomputable def isTerminalSkyscraperPOMPresheafObj (x : X.carrier)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (U : (Opens X.carrier)ᵒᵖ) (h : x ∉ U.unop) :
    IsTerminal ((skyscraperPOM x N).presheaf.obj U) := by
  change IsTerminal ((forget₂ (ModuleCat _) AddCommGrpCat).obj (skyscraperObj x N U))
  rw [skyscraperObj, dite_eq_right h]
  change IsTerminal (AddCommGrpCat.of PUnit.{u+1})
  letI : ∀ Z : AddCommGrpCat.{u}, Unique (Z ⟶ AddCommGrpCat.of PUnit.{u+1}) := fun Z =>
    { default := AddCommGrpCat.ofHom (0 : (↑Z) →+ PUnit)
      uniq := fun g => by ext z }
  exact IsTerminal.ofUnique _

/-- On opens not containing `x`, the sections of the skyscraper presheaf of modules are a
subsingleton. -/
theorem subsingleton_skyscraperPOM_presheaf_obj (x : X.carrier)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (U : (Opens X.carrier)ᵒᵖ) (h : x ∉ U.unop) :
    Subsingleton ((skyscraperPOM x N).presheaf.obj U) := by
  change Subsingleton (↑(skyscraperObj x N U))
  rw [skyscraperObj, dite_eq_right h]
  infer_instance

/-- On an open containing `x`, the sections of the skyscraper presheaf of modules are `N`
with its scalars restricted along the germ map of the structure sheaf. -/
theorem skyscraperObj_eq_of_mem (x : X.carrier) (N : ModuleCat.{u} (X.presheaf.stalk x))
    (U : (Opens X.carrier)ᵒᵖ) (hx : x ∈ U.unop) :
    skyscraperObj x N U =
      (ModuleCat.restrictScalars (X.presheaf.germ U.unop x hx).hom).obj N := by
  rw [skyscraperObj, dite_eq_left hx]

/-- The underlying presheaf of abelian groups of the skyscraper presheaf of modules
`skyscraperPOM x N` is Mathlib's skyscraper presheaf at `x` with value the underlying
additive group of `N`. -/
noncomputable def skyscraperPOMPresheafIso (x : X.carrier)
    [∀ U : Opens X.carrier, Decidable (x ∈ U)]
    (N : ModuleCat.{u} (X.presheaf.stalk x)) :
    (skyscraperPOM x N).presheaf ≅
      skyscraperPresheaf x ((forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).obj N) := by
  classical
  refine NatIso.ofComponents (fun U => ?_) ?_
  · by_cases hx : x ∈ U.unop
    · have hp := skyscraperPOM_presheaf_obj_eq x N U hx
      have hq : (skyscraperPresheaf x
          ((forget₂ (ModuleCat _) AddCommGrpCat).obj N)).obj U = AddCommGrpCat.of (↑N) := by
        simp [skyscraperPresheaf, hx]
      exact eqToIso (hp.trans hq.symm)
    · exact (isTerminalSkyscraperPOMPresheafObj x N U hx).uniqueUpToIso (by
        simpa [skyscraperPresheaf, hx] using (terminalIsTerminal (C := AddCommGrpCat.{u})))
  · intro U V i
    by_cases hxV : x ∈ V.unop
    · have hxU : x ∈ U.unop := (leOfHom i.unop) hxV
      have hgen : ∀ {A B C D E : AddCommGrpCat.{u}} (h₁ : A = B) (h₂ : B = C) (h₃ : C = D)
          (h₄ : A = E) (h₅ : E = D),
          (eqToHom h₁ ≫ eqToHom h₂) ≫ eqToHom h₃ = eqToHom h₄ ≫ eqToHom h₅ := by
        intro A B C D E h₁ h₂ h₃ h₄ h₅
        simp
      simp only [dite_eq_left hxV, dite_eq_left hxU]
      rw [skyscraperPOM_presheaf_map_eq x N i hxV]
      simp only [eqToIso.hom, skyscraperPresheaf_map, dite_eq_left hxV]
      exact hgen _ _ _ _ _
    · have hQ : IsTerminal ((skyscraperPresheaf x
          ((forget₂ (ModuleCat _) AddCommGrpCat).obj N)).obj V) := by
        simpa [skyscraperPresheaf, hxV] using (terminalIsTerminal (C := AddCommGrpCat.{u}))
      simp only [dite_eq_right hxV]
      apply hQ.hom_ext

/-- The canonical identification of the sections of `skyscraperPOM x N` over an open
containing `x` with `N` intertwines the action of the structure sheaf with the action of the
local ring through the germ map.  This is `skyscraperPOM_leg_smul` restated for the module
structure that `PresheafOfModules` puts on the sections of the underlying presheaf of
abelian groups. -/
theorem skyscraperPOM_presheaf_smul (x : X.carrier)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (U : (Opens X.carrier)ᵒᵖ) (hx : x ∈ U.unop)
    (r : (ringSheaf X).obj.obj U) (m : (skyscraperPOM x N).presheaf.obj U) :
    (ConcreteCategory.hom (eqToHom (skyscraperPOM_presheaf_obj_eq x N U hx))) (r • m) =
      (ConcreteCategory.hom (X.presheaf.germ U.unop x hx)) r •
        (ConcreteCategory.hom (eqToHom (skyscraperPOM_presheaf_obj_eq x N U hx))) m :=
  skyscraperPOM_leg_smul x N U hx r m

/-- The underlying presheaf of abelian groups of the pushforward of a skyscraper presheaf of
modules along a morphism of ringed spaces is that of the skyscraper presheaf of modules at the
image point, with the value module restricted along the induced map of stalks. -/
noncomputable def skyscraperPOMPushforwardPresheafIso
    {Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y)
    {φ : (ringSheaf Y).obj ⟶ (Opens.map f.hom.base).op ⋙ (ringSheaf X).obj}
    (x : X.carrier) [∀ U : Opens X.carrier, Decidable (x ∈ U)]
    [∀ V : Opens Y.carrier, Decidable ((ConcreteCategory.hom f.hom.base) x ∈ V)]
    (N : ModuleCat.{u} (X.presheaf.stalk x)) :
    ((PresheafOfModules.pushforward φ).obj (skyscraperPOM x N)).presheaf ≅
      (skyscraperPOM ((ConcreteCategory.hom f.hom.base) x)
        ((ModuleCat.restrictScalars (f.hom.stalkMap x).hom).obj N)).presheaf :=
  eqToIso (PresheafOfModules.pushforward_presheaf φ (skyscraperPOM x N)) ≪≫
    Functor.isoWhiskerLeft (Opens.map f.hom.base).op (skyscraperPOMPresheafIso x N) ≪≫
    eqToIso (skyscraperPresheaf_pushforward_eq f.hom.base x
      ((forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).obj N)) ≪≫
    eqToIso (congrArg (skyscraperPresheaf ((ConcreteCategory.hom f.hom.base) x))
      (ModuleCat.forget₂_restrictScalars_obj (f.hom.stalkMap x).hom N).symm) ≪≫
    (skyscraperPOMPresheafIso ((ConcreteCategory.hom f.hom.base) x)
      ((ModuleCat.restrictScalars (f.hom.stalkMap x).hom).obj N)).symm

/-- The sections of the pushforward of `skyscraperPOM x N` over an open containing the image
of `x` agree with the sections of the skyscraper presheaf of modules at the image point. -/
theorem skyscraperPOM_pushforward_presheaf_obj_eq
    {Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y)
    {φ : (ringSheaf Y).obj ⟶ (Opens.map f.hom.base).op ⋙ (ringSheaf X).obj}
    (x : X.carrier) (N : ModuleCat.{u} (X.presheaf.stalk x))
    (V : (Opens Y.carrier)ᵒᵖ) (hy : (ConcreteCategory.hom f.hom.base) x ∈ V.unop) :
    ((PresheafOfModules.pushforward φ).obj (skyscraperPOM x N)).presheaf.obj V =
      (skyscraperPOM ((ConcreteCategory.hom f.hom.base) x)
        ((ModuleCat.restrictScalars (f.hom.stalkMap x).hom).obj N)).presheaf.obj V := by
  have h1 : ((PresheafOfModules.pushforward φ).obj (skyscraperPOM x N)).presheaf.obj V =
      (skyscraperPOM x N).presheaf.obj (op ((Opens.map f.hom.base).obj V.unop)) := rfl
  exact h1.trans ((skyscraperPOM_presheaf_obj_eq x N _ hy).trans
    ((ModuleCat.addCommGrpCat_of_restrictScalars_obj (f.hom.stalkMap x).hom N).symm.trans
      (skyscraperPOM_presheaf_obj_eq _ _ V hy).symm))

/-- Over an open containing the image of `x`, `skyscraperPOMPushforwardPresheafIso` is the
canonical identification of the two descriptions of the sections. -/
theorem skyscraperPOMPushforwardPresheafIso_hom_app
    {Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y)
    {φ : (ringSheaf Y).obj ⟶ (Opens.map f.hom.base).op ⋙ (ringSheaf X).obj}
    (x : X.carrier) [∀ U : Opens X.carrier, Decidable (x ∈ U)]
    [∀ V : Opens Y.carrier, Decidable ((ConcreteCategory.hom f.hom.base) x ∈ V)]
    (N : ModuleCat.{u} (X.presheaf.stalk x))
    (V : (Opens Y.carrier)ᵒᵖ) (hy : (ConcreteCategory.hom f.hom.base) x ∈ V.unop) :
    (skyscraperPOMPushforwardPresheafIso f (φ := φ) x N).hom.app V =
      eqToHom (skyscraperPOM_pushforward_presheaf_obj_eq f (φ := φ) x N V hy) := by
  have hx : x ∈ unop ((Opens.map f.hom.base).op.obj V) := hy
  simp only [skyscraperPOMPushforwardPresheafIso, Iso.trans_hom, NatTrans.comp_app,
    eqToIso.hom, eqToHom_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom,
    skyscraperPOMPresheafIso, NatIso.ofComponents_inv_app, NatIso.ofComponents_hom_app,
    dite_eq_left hx, dite_eq_left hy, eqToIso.inv, eqToHom_trans]

/-- On an open containing the image of `x`, the module of sections of the pushforward of
`skyscraperPOM x N` *is* the module of sections of the skyscraper presheaf of modules at the
image point: both are `N` with scalars restricted along the same ring map, by compatibility of
the germ maps with the map on stalks. -/
theorem skyscraperPOM_pushforward_obj_eq
    {Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y)
    {φ : (ringSheaf Y).obj ⟶ (Opens.map f.hom.base).op ⋙ (ringSheaf X).obj}
    (x : X.carrier) (N : ModuleCat.{u} (X.presheaf.stalk x))
    (V : (Opens Y.carrier)ᵒᵖ) (hy : (ConcreteCategory.hom f.hom.base) x ∈ V.unop)
    (hg : (X.presheaf.germ ((Opens.map f.hom.base).obj V.unop) x hy).hom.comp (φ.app V).hom =
      (f.hom.stalkMap x).hom.comp
        (Y.presheaf.germ V.unop ((ConcreteCategory.hom f.hom.base) x) hy).hom) :
    ((PresheafOfModules.pushforward φ).obj (skyscraperPOM x N)).obj V =
      (skyscraperPOM ((ConcreteCategory.hom f.hom.base) x)
        ((ModuleCat.restrictScalars (f.hom.stalkMap x).hom).obj N)).obj V := by
  have h1 : ((PresheafOfModules.pushforward φ).obj (skyscraperPOM x N)).obj V =
      (ModuleCat.restrictScalars (φ.app V).hom).obj
        (skyscraperObj x N (op ((Opens.map f.hom.base).obj V.unop))) := rfl
  have h2 : (skyscraperPOM ((ConcreteCategory.hom f.hom.base) x)
        ((ModuleCat.restrictScalars (f.hom.stalkMap x).hom).obj N)).obj V =
      skyscraperObj ((ConcreteCategory.hom f.hom.base) x)
        ((ModuleCat.restrictScalars (f.hom.stalkMap x).hom).obj N) V := rfl
  rw [h1, h2, skyscraperObj_eq_of_mem x N _ hy,
    skyscraperObj_eq_of_mem ((ConcreteCategory.hom f.hom.base) x) _ V hy]
  exact congrArg (fun g => (ModuleCat.restrictScalars g).obj N) hg

section Pushforward

variable {Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y)
  {φ : (ringSheaf Y).obj ⟶ (Opens.map f.hom.base).op ⋙ (ringSheaf X).obj}
  (x : X.carrier) [∀ U : Opens X.carrier, Decidable (x ∈ U)]
  [∀ V : Opens Y.carrier, Decidable ((ConcreteCategory.hom f.hom.base) x ∈ V)]
  (N : ModuleCat.{u} (X.presheaf.stalk x))

/-- Compatibility of the structure map `φ` with the germ maps, the hypothesis under which the
pushforward of a skyscraper module is again a skyscraper module.  For the structure map of a
morphism of ringed spaces this is `PresheafedSpace.stalkMap_germ`. -/
def SkyscraperPushforwardCompatible : Prop :=
  ∀ (V : (Opens Y.carrier)ᵒᵖ) (hy : (ConcreteCategory.hom f.hom.base) x ∈ V.unop),
    (X.presheaf.germ ((Opens.map f.hom.base).obj V.unop) x hy).hom.comp (φ.app V).hom =
      (f.hom.stalkMap x).hom.comp
        (Y.presheaf.germ V.unop ((ConcreteCategory.hom f.hom.base) x) hy).hom

/-- The comparison map of underlying presheaves of `skyscraperPOMPushforwardPresheafIso` is
semilinear over the structure sheaf, hence defines a morphism of presheaves of modules. -/
theorem skyscraperPOMPushforwardPresheafIso_hom_app_smul
    (hg : SkyscraperPushforwardCompatible f (φ := φ) x)
    (V : (Opens Y.carrier)ᵒᵖ) (r : (ringSheaf Y).obj.obj V)
    (m : ((PresheafOfModules.pushforward φ).obj (skyscraperPOM x N)).obj V) :
    (skyscraperPOMPushforwardPresheafIso f (φ := φ) x N).hom.app V (r • m) =
      r • (skyscraperPOMPushforwardPresheafIso f (φ := φ) x N).hom.app V m := by
  classical
  have hcast : ∀ {A B : AddCommGrpCat.{u}} (hab : A = B) (y : A),
      (ConcreteCategory.hom (eqToHom hab)) y =
        cast (congrArg (fun Z : AddCommGrpCat.{u} => (↑Z : Type u)) hab) y := by
    intro A B hab y
    subst hab
    simp
  by_cases hy : (ConcreteCategory.hom f.hom.base) x ∈ V.unop
  · rw [skyscraperPOMPushforwardPresheafIso_hom_app f x N V hy]
    have hab := skyscraperPOM_pushforward_presheaf_obj_eq f (φ := φ) x N V hy
    exact (hcast hab (r • m)).trans
      ((ModuleCat.cast_smul_of_eq
          (skyscraperPOM_pushforward_obj_eq f (φ := φ) x N V hy (hg V hy)) _ r m).trans
        (congrArg (fun z => r • z) (hcast hab m).symm))
  · exact (subsingleton_skyscraperPOM_presheaf_obj
      ((ConcreteCategory.hom f.hom.base) x) _ V hy).elim _ _

/-- The comparison morphism of presheaves of modules from the pushforward of a skyscraper
module to the skyscraper module at the image point. -/
noncomputable def skyscraperPOMPushforwardMap
    (hg : SkyscraperPushforwardCompatible f (φ := φ) x) :
    (PresheafOfModules.pushforward φ).obj (skyscraperPOM x N) ⟶
      skyscraperPOM ((ConcreteCategory.hom f.hom.base) x)
        ((ModuleCat.restrictScalars (f.hom.stalkMap x).hom).obj N) :=
  PresheafOfModules.homMk (skyscraperPOMPushforwardPresheafIso f (φ := φ) x N).hom
    (skyscraperPOMPushforwardPresheafIso_hom_app_smul f x N hg)

/-- `skyscraperPOMPushforwardMap` is `skyscraperPOMPushforwardPresheafIso` on underlying
presheaves of abelian groups. -/
theorem skyscraperPOMPushforwardMap_forget₂_app
    (hg : SkyscraperPushforwardCompatible f (φ := φ) x) (V : (Opens Y.carrier)ᵒᵖ) :
    (forget₂ (ModuleCat ((ringSheaf Y).obj.obj V)) AddCommGrpCat).map
        ((skyscraperPOMPushforwardMap f x N hg).app V) =
      (skyscraperPOMPushforwardPresheafIso f (φ := φ) x N).hom.app V := rfl

/-- **The pushforward of a skyscraper module is a skyscraper module.**  For a morphism
`f : X ⟶ Y` of ringed spaces whose structure map `φ` on sections is compatible with the germ
maps (`hg`, which holds for the structure map of `f` by `PresheafedSpace.stalkMap_germ`), the
pushforward along `f` of the skyscraper presheaf of modules at `x` with value `N` is the
skyscraper presheaf of modules at `f x` with value `N` viewed over `𝒪_{Y, f x}` through the
induced map of stalks. -/
noncomputable def skyscraperPOMPushforwardIso
    (hg : SkyscraperPushforwardCompatible f (φ := φ) x) :
    (PresheafOfModules.pushforward φ).obj (skyscraperPOM x N) ≅
      skyscraperPOM ((ConcreteCategory.hom f.hom.base) x)
        ((ModuleCat.restrictScalars (f.hom.stalkMap x).hom).obj N) :=
  haveI hiso : ∀ V : (Opens Y.carrier)ᵒᵖ,
      IsIso ((skyscraperPOMPushforwardMap f x N hg).app V) := fun V => by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ConcreteCategory.bijective_of_isIso
      ((skyscraperPOMPushforwardPresheafIso f (φ := φ) x N).hom.app V)
  PresheafOfModules.isoMk (fun V => asIso ((skyscraperPOMPushforwardMap f x N hg).app V))
    (fun _ _ i => (skyscraperPOMPushforwardMap f x N hg).naturality i)

/-- `skyscraperPOMPushforwardIso` has `skyscraperPOMPushforwardMap` as its forward map. -/
theorem skyscraperPOMPushforwardIso_hom_app
    (hg : SkyscraperPushforwardCompatible f (φ := φ) x) (V : (Opens Y.carrier)ᵒᵖ) :
    (skyscraperPOMPushforwardIso f x N hg).hom.app V =
      (skyscraperPOMPushforwardMap f x N hg).app V := rfl

end Pushforward

end OXModule

end SkyscraperSections
