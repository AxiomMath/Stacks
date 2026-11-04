module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Topology.Sheaves.CommRingCat
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import StacksCore.Tactic.StacksAttribute

/-!
# The skyscraper sheaf of modules at a point

Let `X` be a topological space, `𝒪` a presheaf of commutative rings on `X` and `z` a point of
`X`. For an `𝒪_z`-module `V` the *skyscraper* `i_{z,*} V` is the sheaf of `𝒪`-modules whose
sections over `U` are `V` if `z ∈ U` and zero otherwise, the `𝒪(U)`-action being given by the
germ map at `z`. This file constructs it and proves the adjunction

`Hom_{𝒪_z}(ℱ_z, V) ≃ Hom_𝒪(ℱ, i_{z,*} V)`

of [Stacks Project, Tag 009C] for sheaves of modules, the one case of that tag which is not an
instance of the construction for sheaves valued in a fixed category.

## Main definitions

* `Stacks.Modules.skyscraperAbPresheaf` is the underlying presheaf of abelian groups, with
  sections `PLift (z ∈ U) → V` over `U`.
* `Stacks.Modules.skyscraperPresheaf` is the skyscraper as a presheaf of modules.
* `Stacks.Modules.skyscraper` is the skyscraper as a sheaf of modules.
* `Stacks.Modules.skyscraperFunctor` is the skyscraper as a functor in the value `V`, and
  `Stacks.Modules.stalkSheafFunctor` is the stalk at `z` as a functor valued in `𝒪_z`-modules.

## Main results

* `Stacks.Modules.skyscraperPresheafHomEquiv` and `Stacks.Modules.skyscraperHomEquiv` are the
  adjunction bijections at the presheaf and sheaf level.
* `Stacks.Modules.stalkSkyscraperPresheafAdjunction` and
  `Stacks.Modules.stalkSkyscraperAdjunction` assemble the bijection into an adjunction between
  the stalk functor and the skyscraper functor, at the presheaf and the sheaf level.

## Implementation notes

Sections over `U` are modelled as functions on the *proposition* `z ∈ U`, lifted to a type by
`PLift` because the `Pi` algebra instances of Mathlib are indexed by a `Type`. This avoids the
`if z ∈ U then V else 0` form of `skyscraperPresheaf`, whose `eqToHom`s would have to be carried
through every computation, and it makes the restriction maps plain reindexings: both the
functoriality of the presheaf and the naturality of every cocone below hold by `rfl`, using
definitional proof irrelevance for the membership proofs.

The `𝒪(U)`-module structure on the sections is `Pi.module` applied to the family of module
structures `Module.compHom V (𝒪.germ U z h)` indexed by the membership proof `h`. The germ map
exists only in the presence of such a proof, which is exactly why the `Pi`-over-a-proposition
form is the convenient one: no case distinction on `z ∈ U` is ever made.

Everything below the sheaf condition is stated for a *presheaf* of commutative rings `𝒪`, so
that the module structure on a stalk supplied by `Mathlib.Algebra.Category.ModuleCat.Stalk` is
found by instance search: it is declared for `PresheafOfModules (𝒪 ⋙ forget₂ _ _)` and that
shape has to appear syntactically.

## References

* [Stacks Project, Tag 009A](https://stacks.math.columbia.edu/tag/009A)
* [Stacks Project, Tag 009C](https://stacks.math.columbia.edu/tag/009C)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite Limits

universe u

namespace Stacks.Modules

variable {X : TopCat.{u}}

/-! ### The underlying presheaf of abelian groups -/

/-- The underlying presheaf of abelian groups of the skyscraper at `z` with value `V`: its
sections over `U` are the functions on the proposition `z ∈ U` with values in `V`. -/
noncomputable def skyscraperAbPresheaf (z : X) (V : Ab.{u}) : X.Presheaf Ab.{u} where
  obj U := AddCommGrpCat.of (PLift (z ∈ U.unop) → V)
  map {_ _} f := AddCommGrpCat.ofHom
    { toFun := fun g h => g ⟨f.unop.le h.down⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

/-- Restriction in the skyscraper presheaf of abelian groups precomposes a section with the
inclusion of membership proofs. -/
@[simp]
lemma skyscraperAbPresheaf_map_apply (z : X) (V : Ab.{u}) {U W : (Opens X)ᵒᵖ} (f : U ⟶ W)
    (g : (skyscraperAbPresheaf z V).obj U) (h : PLift (z ∈ W.unop)) :
    (skyscraperAbPresheaf z V).map f g h = g ⟨f.unop.le h.down⟩ := rfl

/-- The skyscraper presheaf of abelian groups is a sheaf: a compatible family of sections over
a covering family of `U` is determined by, and determines, a value at any one member of the
family containing `z`. -/
lemma skyscraperAbPresheaf_isSheaf (z : X) (V : Ab.{u}) :
    (skyscraperAbPresheaf z V).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf cpt
  choose c hc using fun h : PLift (z ∈ iSup U) => Opens.mem_iSup.mp h.down
  have key : ∀ (h : PLift (z ∈ iSup U)) (j : ι) (hj : PLift (z ∈ U j)),
      sf (c h) ⟨hc h⟩ = sf j hj :=
    fun h j hj => congrFun (cpt (c h) j) ⟨⟨hc h, hj.down⟩⟩
  exact ⟨fun h => sf (c h) ⟨hc h⟩, fun i => funext fun h => key ⟨le_iSup U i h.down⟩ i h,
    fun s hs => funext fun h => congrFun (hs (c h)) ⟨hc h⟩⟩

/-- The cocone on the neighbourhood diagram of `z` which evaluates a section of the skyscraper
at the membership proof carried by the neighbourhood. -/
noncomputable def skyscraperAbStalkCocone (z : X) (V : Ab.{u}) :
    Cocone ((OpenNhds.inclusion z).op ⋙ skyscraperAbPresheaf z V) where
  pt := V
  ι :=
    { app := fun U => AddCommGrpCat.ofHom
        (AddMonoidHom.mk' (fun g : PLift (z ∈ U.unop.1) → V => g ⟨U.unop.2⟩) (fun _ _ => rfl))
      naturality := fun _ _ _ => rfl }

/-- Evaluation of a germ at `z` of the skyscraper presheaf at `z`: the inverse of the
isomorphism `V ≅ (i_{z,*} V)_z`, as a map of abelian groups. -/
noncomputable def skyscraperAbStalkEval (z : X) (V : Ab.{u}) :
    (skyscraperAbPresheaf z V).stalk z ⟶ V :=
  colimit.desc _ (skyscraperAbStalkCocone z V)

/-- Evaluating the germ at `z` of a section `g` over `U ∋ z` gives the value of `g` at the proof
of `z ∈ U`. -/
@[simp]
lemma skyscraperAbStalkEval_germ (z : X) (V : Ab.{u}) (U : Opens X) (hU : z ∈ U)
    (g : (skyscraperAbPresheaf z V).obj (op U)) :
    skyscraperAbStalkEval z V ((skyscraperAbPresheaf z V).germ U z hU g) = g ⟨hU⟩ := by
  rw [← ConcreteCategory.comp_apply]
  exact ConcreteCategory.congr_hom
    (colimit.ι_desc (skyscraperAbStalkCocone z V) (op ⟨U, hU⟩)) g

/-! ### The module structure -/

variable (O : X.Presheaf CommRingCat.{u}) (z : X) (V : ModuleCat.{u} ↑(O.stalk z))

/-- The `𝒪(U)`-module structure on the sections of the skyscraper over `U`: a scalar acts on
the value at a membership proof `h` through the germ map at `z` determined by `h`. -/
@[instance_reducible]
noncomputable def skyscraperModuleSections (U : (Opens X)ᵒᵖ) :
    Module ↑((O ⋙ forget₂ CommRingCat RingCat.{u}).obj U)
      ((skyscraperAbPresheaf z (AddCommGrpCat.of ↑V)).obj U) :=
  @Pi.module (PLift (z ∈ U.unop)) (fun _ => ↑V)
    ↑((O ⋙ forget₂ CommRingCat RingCat.{u}).obj U) _ _
    (fun h => Module.compHom ↑V (O.germ U.unop z h.down).hom)

attribute [local instance] skyscraperModuleSections

/-- A scalar `r` of `𝒪(U)` acts on the value of a section at a proof `h` of `z ∈ U` through the
germ of `r` at `z`. -/
@[simp]
lemma skyscraperModuleSections_smul_apply (U : (Opens X)ᵒᵖ)
    (r : ↑((O ⋙ forget₂ CommRingCat RingCat.{u}).obj U))
    (g : (skyscraperAbPresheaf z (AddCommGrpCat.of ↑V)).obj U) (h : PLift (z ∈ U.unop)) :
    (r • g) h = (O.germ U.unop z h.down) r • g h := rfl

/-- The skyscraper at `z` with value `V`, as a presheaf of `𝒪`-modules. -/
noncomputable def skyscraperPresheaf :
    PresheafOfModules.{u} (O ⋙ forget₂ CommRingCat RingCat.{u}) :=
  PresheafOfModules.ofPresheaf (skyscraperAbPresheaf z (AddCommGrpCat.of ↑V))
    (fun {U W} f r m => funext fun h => by
      rw [skyscraperAbPresheaf_map_apply, skyscraperModuleSections_smul_apply,
        skyscraperModuleSections_smul_apply, skyscraperAbPresheaf_map_apply]
      exact congrArg (· • m ⟨f.unop.le h.down⟩) (O.germ_res_apply f.unop z h.down r).symm)

/-- The underlying presheaf of abelian groups of `skyscraperPresheaf O z V` is
`skyscraperAbPresheaf z V`. -/
@[simp]
lemma skyscraperPresheaf_presheaf :
    (skyscraperPresheaf O z V).presheaf = skyscraperAbPresheaf z (AddCommGrpCat.of ↑V) := rfl


/-! ### The adjunction at the level of presheaves of modules -/

variable (G : PresheafOfModules.{u} (O ⋙ forget₂ CommRingCat RingCat.{u}))

/-- The morphism of presheaves of modules into the skyscraper determined by a linear map out of
the stalk at `z`: a section over `U` is sent to the function whose value at a proof of `z ∈ U`
is the image of its germ. -/
noncomputable def skyscraperPresheafHom
    (φ : ↑(TopCat.Presheaf.stalk G.presheaf z) →ₗ[↑(O.stalk z)] ↑V) :
    G ⟶ skyscraperPresheaf O z V :=
  PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom
        (AddMonoidHom.mk'
          (fun s => (fun h => φ (TopCat.Presheaf.germ G.presheaf U.unop z h.down s) :
            PLift (z ∈ U.unop) → ↑V))
          (fun a b => funext fun h =>
            (congrArg φ (map_add (TopCat.Presheaf.germ G.presheaf U.unop z h.down).hom a b)).trans
              (map_add φ _ _)))
      naturality := fun {U W} f => by
        ext s
        funext h
        exact congrArg φ (TopCat.Presheaf.germ_res_apply G.presheaf f.unop z h.down s) }
    (fun U r m => funext fun h =>
      (congrArg φ (PresheafOfModules.germ_smul G z U.unop h.down r m)).trans
        (map_smul φ _ _))

/-- The value of `skyscraperPresheafHom φ` on a section `s` over `U ∋ z` is `φ` of the germ of
`s` at `z`. -/
lemma skyscraperPresheafHom_app_apply
    (φ : ↑(TopCat.Presheaf.stalk G.presheaf z) →ₗ[↑(O.stalk z)] ↑V) (U : Opens X) (hU : z ∈ U)
    (s : ↑(G.presheaf.obj (op U))) :
    (skyscraperPresheafHom O z V G φ).app (op U) s ⟨hU⟩ =
      φ (TopCat.Presheaf.germ G.presheaf U z hU s) := by rfl

/-- The map of abelian groups out of the stalk underlying
`Stacks.Modules.stalkMapOfSkyscraperPresheafHom`. -/
noncomputable def skyscraperStalkMapAux (ψ : G ⟶ skyscraperPresheaf O z V) :
    TopCat.Presheaf.stalk G.presheaf z ⟶ AddCommGrpCat.of ↑V :=
  (TopCat.Presheaf.stalkFunctor Ab.{u} z).map ((PresheafOfModules.toPresheaf _).map ψ) ≫
    skyscraperAbStalkEval z (AddCommGrpCat.of ↑V)

/-- `skyscraperStalkMapAux ψ` sends the germ at `z` of a section `s` over `U ∋ z` to the value
of `ψ s` at the proof of `z ∈ U`. -/
lemma skyscraperStalkMapAux_germ (ψ : G ⟶ skyscraperPresheaf O z V) (U : Opens X) (hU : z ∈ U)
    (s : ↑(G.presheaf.obj (op U))) :
    skyscraperStalkMapAux O z V G ψ (TopCat.Presheaf.germ G.presheaf U z hU s) =
      ψ.app (op U) s ⟨hU⟩ := by
  refine Eq.trans (congrArg (fun x => skyscraperAbStalkEval z (AddCommGrpCat.of ↑V) x)
    (TopCat.Presheaf.stalkFunctor_map_germ_apply U z hU
      ((PresheafOfModules.toPresheaf _).map ψ) s)) ?_
  exact skyscraperAbStalkEval_germ z _ U hU _

/-- `skyscraperStalkMapAux ψ` is `𝒪_z`-linear. -/
lemma skyscraperStalkMapAux_smul (ψ : G ⟶ skyscraperPresheaf O z V) (r : ↑(O.stalk z))
    (m : ↑(TopCat.Presheaf.stalk G.presheaf z)) :
    skyscraperStalkMapAux O z V G ψ (r • m) = r • skyscraperStalkMapAux O z V G ψ m := by
  obtain ⟨U, hU, r', rfl⟩ := TopCat.Presheaf.exists_germ_eq O r
  obtain ⟨W, hW, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq G.presheaf m
  have hT : z ∈ U ⊓ W := ⟨hU, hW⟩
  have e1 : O.germ U z hU r' =
      O.germ (U ⊓ W) z hT (O.map (Opens.infLELeft U W).op r') :=
    (O.germ_res_apply (Opens.infLELeft U W) z hT r').symm
  have e2 : TopCat.Presheaf.germ G.presheaf W z hW s =
      TopCat.Presheaf.germ G.presheaf (U ⊓ W) z hT
        (G.presheaf.map (Opens.infLERight U W).op s) :=
    (TopCat.Presheaf.germ_res_apply G.presheaf (Opens.infLERight U W) z hT s).symm
  rw [e1, e2]
  refine Eq.trans (congrArg (fun x => skyscraperStalkMapAux O z V G ψ x)
    (PresheafOfModules.germ_smul G z (U ⊓ W) hT (O.map (Opens.infLELeft U W).op r')
      (G.presheaf.map (Opens.infLERight U W).op s)).symm) ?_
  refine Eq.trans (skyscraperStalkMapAux_germ O z V G ψ (U ⊓ W) hT _) ?_
  refine Eq.trans (congrFun (map_smul (ψ.app (op (U ⊓ W))).hom _ _) ⟨hT⟩) ?_
  exact congrArg (fun y => O.germ (U ⊓ W) z hT (O.map (Opens.infLELeft U W).op r') • y)
    (skyscraperStalkMapAux_germ O z V G ψ (U ⊓ W) hT _).symm

/-- The linear map out of the stalk at `z` determined by a morphism of presheaves of modules
into the skyscraper at `z`. -/
noncomputable def stalkMapOfSkyscraperPresheafHom (ψ : G ⟶ skyscraperPresheaf O z V) :
    ↑(TopCat.Presheaf.stalk G.presheaf z) →ₗ[↑(O.stalk z)] ↑V where
  toFun := skyscraperStalkMapAux O z V G ψ
  map_add' := map_add (skyscraperStalkMapAux O z V G ψ).hom
  map_smul' := skyscraperStalkMapAux_smul O z V G ψ

/-- `stalkMapOfSkyscraperPresheafHom ψ` sends the germ at `z` of a section `s` over `U ∋ z` to
the value of `ψ s` at the proof of `z ∈ U`. -/
lemma stalkMapOfSkyscraperPresheafHom_germ (ψ : G ⟶ skyscraperPresheaf O z V) (U : Opens X)
    (hU : z ∈ U) (s : ↑(G.presheaf.obj (op U))) :
    stalkMapOfSkyscraperPresheafHom O z V G ψ (TopCat.Presheaf.germ G.presheaf U z hU s) =
      ψ.app (op U) s ⟨hU⟩ :=
  skyscraperStalkMapAux_germ O z V G ψ U hU s

/-- **Stacks 009C for sheaves of modules, at the level of presheaves.** Morphisms of presheaves
of `𝒪`-modules from `ℱ` into the skyscraper at `z` with value `V` are the same as
`𝒪_z`-linear maps `ℱ_z ⟶ V`. -/
noncomputable def skyscraperPresheafHomEquiv :
    (G ⟶ skyscraperPresheaf O z V) ≃
      (↑(TopCat.Presheaf.stalk G.presheaf z) →ₗ[↑(O.stalk z)] ↑V) where
  toFun := stalkMapOfSkyscraperPresheafHom O z V G
  invFun := skyscraperPresheafHom O z V G
  left_inv ψ := by
    refine PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext
      (LinearMap.ext fun s => funext fun h => ?_)
    exact stalkMapOfSkyscraperPresheafHom_germ O z V G ψ U.unop h.down s
  right_inv φ := by
    refine LinearMap.ext fun m => ?_
    obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq G.presheaf m
    exact stalkMapOfSkyscraperPresheafHom_germ O z V G _ U hU s

/-! ### Functoriality in the value -/

/-- Postcomposition with a linear map, as a morphism of skyscraper presheaves of modules. -/
noncomputable def skyscraperPresheafMap {V W : ModuleCat.{u} ↑(O.stalk z)} (φ : V ⟶ W) :
    skyscraperPresheaf O z V ⟶ skyscraperPresheaf O z W :=
  PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom
        (AddMonoidHom.mk' (fun g : PLift (z ∈ U.unop) → ↑V => fun h => φ (g h))
          (fun a b => funext fun h => map_add φ.hom (a h) (b h)))
      naturality := by intros; rfl }
    (fun U r m => funext fun h => map_smul φ.hom _ _)

/-- `skyscraperPresheafMap φ` applies `φ` to the value of a section at each membership proof. -/
lemma skyscraperPresheafMap_app_apply {V W : ModuleCat.{u} ↑(O.stalk z)} (φ : V ⟶ W)
    (U : (Opens X)ᵒᵖ) (g : (skyscraperAbPresheaf z (AddCommGrpCat.of ↑V)).obj U)
    (h : PLift (z ∈ U.unop)) :
    (skyscraperPresheafMap O z φ).app U g h = φ (g h) := by rfl

/-! ### The stalk functor and the adjunction, at the level of presheaves of modules -/

section PresheafAdjunction

variable {O z}

/-- The map induced on stalks at `z` by a morphism of presheaves of modules, as an
`𝒪_z`-linear map. -/
noncomputable def stalkLinearMap {G H : PresheafOfModules.{u} (O ⋙ forget₂ CommRingCat RingCat.{u})}
    (ψ : G ⟶ H) :
    ↑(TopCat.Presheaf.stalk G.presheaf z) →ₗ[↑(O.stalk z)]
      ↑(TopCat.Presheaf.stalk H.presheaf z) where
  toFun := (TopCat.Presheaf.stalkFunctor Ab.{u} z).map ((PresheafOfModules.toPresheaf _).map ψ)
  map_add' := map_add
    ((TopCat.Presheaf.stalkFunctor Ab.{u} z).map ((PresheafOfModules.toPresheaf _).map ψ)).hom
  map_smul' r m := by
    obtain ⟨U, hU, r', rfl⟩ := TopCat.Presheaf.exists_germ_eq O r
    obtain ⟨W, hW, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq G.presheaf m
    have hT : z ∈ U ⊓ W := ⟨hU, hW⟩
    have e1 : O.germ U z hU r' =
        O.germ (U ⊓ W) z hT (O.map (Opens.infLELeft U W).op r') :=
      (O.germ_res_apply (Opens.infLELeft U W) z hT r').symm
    have e2 : TopCat.Presheaf.germ G.presheaf W z hW s =
        TopCat.Presheaf.germ G.presheaf (U ⊓ W) z hT
          (G.presheaf.map (Opens.infLERight U W).op s) :=
      (TopCat.Presheaf.germ_res_apply G.presheaf (Opens.infLERight U W) z hT s).symm
    rw [e1, e2]
    refine Eq.trans (congrArg
      (fun x => (TopCat.Presheaf.stalkFunctor Ab.{u} z).map
        ((PresheafOfModules.toPresheaf _).map ψ) x)
      (PresheafOfModules.germ_smul G z (U ⊓ W) hT (O.map (Opens.infLELeft U W).op r')
        (G.presheaf.map (Opens.infLERight U W).op s)).symm) ?_
    refine Eq.trans (TopCat.Presheaf.stalkFunctor_map_germ_apply (U ⊓ W) z hT _ _) ?_
    refine Eq.trans (congrArg (TopCat.Presheaf.germ H.presheaf (U ⊓ W) z hT)
      (map_smul (ψ.app (op (U ⊓ W))).hom _ _)) ?_
    refine Eq.trans (PresheafOfModules.germ_smul H z (U ⊓ W) hT _ _) ?_
    exact congrArg (fun y => O.germ (U ⊓ W) z hT (O.map (Opens.infLELeft U W).op r') • y)
      (TopCat.Presheaf.stalkFunctor_map_germ_apply (U ⊓ W) z hT
        ((PresheafOfModules.toPresheaf _).map ψ)
        (G.presheaf.map (Opens.infLERight U W).op s)).symm

/-- `stalkLinearMap ψ` sends the germ at `z` of a section `s` to the germ at `z` of `ψ s`. -/
lemma stalkLinearMap_germ
    {G H : PresheafOfModules.{u} (O ⋙ forget₂ CommRingCat RingCat.{u})} (ψ : G ⟶ H)
    (U : Opens X) (hU : z ∈ U) (s : ↑(G.presheaf.obj (op U))) :
    stalkLinearMap ψ (TopCat.Presheaf.germ G.presheaf U z hU s) =
      TopCat.Presheaf.germ H.presheaf U z hU (ψ.app (op U) s) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U z hU _ s

variable (O z)

/-- The stalk at `z` as a functor from presheaves of `𝒪`-modules to `𝒪_z`-modules. -/
noncomputable def stalkPresheafFunctor :
    PresheafOfModules.{u} (O ⋙ forget₂ CommRingCat RingCat.{u}) ⥤
      ModuleCat.{u} ↑(O.stalk z) where
  obj G := ModuleCat.of _ ↑(TopCat.Presheaf.stalk G.presheaf z)
  map ψ := ModuleCat.ofHom (stalkLinearMap ψ)
  map_id G := ModuleCat.hom_ext (LinearMap.ext fun m => by
    obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq G.presheaf m
    exact stalkLinearMap_germ (𝟙 G) U hU s)
  map_comp := fun {G _ _} ψ χ => ModuleCat.hom_ext (LinearMap.ext fun m => by
    obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq G.presheaf m
    refine Eq.trans (stalkLinearMap_germ (ψ ≫ χ) U hU s) ?_
    exact ((congrArg (stalkLinearMap χ) (stalkLinearMap_germ ψ U hU s)).trans
      (stalkLinearMap_germ χ U hU _)).symm)

/-- The skyscraper at `z` as a functor from `𝒪_z`-modules to presheaves of `𝒪`-modules. -/
noncomputable def skyscraperPresheafFunctor :
    ModuleCat.{u} ↑(O.stalk z) ⥤
      PresheafOfModules.{u} (O ⋙ forget₂ CommRingCat RingCat.{u}) where
  obj V := skyscraperPresheaf O z V
  map φ := skyscraperPresheafMap O z φ
  map_id _ := PresheafOfModules.hom_ext fun _ => ModuleCat.hom_ext
    (LinearMap.ext fun _ => funext fun _ => rfl)
  map_comp _ _ := PresheafOfModules.hom_ext fun _ => ModuleCat.hom_ext
    (LinearMap.ext fun _ => funext fun _ => rfl)

/-- **Stacks 009C for presheaves of modules.** The stalk functor at `z` is left adjoint to the
skyscraper functor at `z`. -/
noncomputable def stalkSkyscraperPresheafAdjunction :
    stalkPresheafFunctor O z ⊣ skyscraperPresheafFunctor O z :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun G V =>
        (ModuleCat.homEquiv (M := (stalkPresheafFunctor O z).obj G) (N := V)).trans
          (skyscraperPresheafHomEquiv O z V G).symm
      homEquiv_naturality_left_symm := fun {G' G V} χ φ => by
        refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
        obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq G'.presheaf m
        refine Eq.trans (stalkMapOfSkyscraperPresheafHom_germ O z V G' (χ ≫ φ) U hU s) ?_
        exact ((congrArg (stalkMapOfSkyscraperPresheafHom O z V G φ)
            (stalkLinearMap_germ χ U hU s)).trans
          (stalkMapOfSkyscraperPresheafHom_germ O z V G φ U hU _)).symm
      homEquiv_naturality_right := fun {G V V'} φ ν => by
        refine PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext
          (LinearMap.ext fun s => funext fun _ => rfl) }

end PresheafAdjunction

/-! ### The skyscraper sheaf of modules -/

end Stacks.Modules

namespace Stacks.Modules

open CategoryTheory TopologicalSpace Opposite Limits

variable {X : TopCat.{u}} (R : TopCat.Sheaf CommRingCat.{u} X) (z : X)
  (V : ModuleCat.{u} ↑(TopCat.Presheaf.stalk R.obj z))

/-- **Stacks 009A (4).** The skyscraper sheaf of `𝒪_X`-modules at the point `z` with value the
`𝒪_{X,z}`-module `V`: the pushforward of `V` along the inclusion of `z`, read as a morphism of
ringed spaces `({z}, 𝒪_{X,z}) ⟶ (X, 𝒪_X)`. -/
@[stacks 009A "(4)"]
noncomputable def skyscraper :
    SheafOfModules.{u} ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R) where
  val := skyscraperPresheaf R.obj z V
  isSheaf := skyscraperAbPresheaf_isSheaf z _

/-- The `𝒪_{X,z}`-module structure on the stalk at `z` of a sheaf of `𝒪_X`-modules. It is
Mathlib's instance for presheaves of modules, which instance search does not find at a sheaf
of modules because the base `(sheafCompose _ (forget₂ _ _)).obj R` is not syntactically of the
form `𝒪 ⋙ forget₂ _ _`. -/
@[instance_reducible]
noncomputable def stalkModule
    (G : SheafOfModules.{u} ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R)) :
    Module ↑(TopCat.Presheaf.stalk R.obj z) ↑(TopCat.Presheaf.stalk G.val.presheaf z) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := R.obj) G.val z

attribute [local instance] stalkModule

/-- A morphism of sheaves of modules is the same thing as a morphism of the underlying
presheaves of modules. -/
def homValEquiv
    (G H : SheafOfModules.{u} ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R)) :
    (G ⟶ H) ≃ (G.val ⟶ H.val) where
  toFun ψ := ψ.val
  invFun ψ := ⟨ψ⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Stacks 009C for sheaves of modules.** Morphisms of sheaves of `𝒪_X`-modules from `ℱ` into
the skyscraper at `z` with value `V` are the same thing as `𝒪_{X,z}`-linear maps `ℱ_z ⟶ V`;
this is the adjunction between the stalk functor and the skyscraper functor. -/
@[stacks 009C "sheaves of modules"]
noncomputable def skyscraperHomEquiv
    (G : SheafOfModules.{u} ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R)) :
    (G ⟶ skyscraper R z V) ≃
      (↑(TopCat.Presheaf.stalk G.val.presheaf z) →ₗ[↑(TopCat.Presheaf.stalk R.obj z)] ↑V) :=
  (homValEquiv R G (skyscraper R z V)).trans (skyscraperPresheafHomEquiv R.obj z V G.val)

/-- The linear map `skyscraperHomEquiv ψ` sends the germ at `z` of a section `s` over `U ∋ z` to
the value of `ψ s` at the proof of `z ∈ U`. -/
lemma skyscraperHomEquiv_germ
    (G : SheafOfModules.{u} ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R))
    (ψ : G ⟶ skyscraper R z V) (U : Opens X) (hU : z ∈ U)
    (s : ↑(G.val.presheaf.obj (op U))) :
    skyscraperHomEquiv R z V G ψ (TopCat.Presheaf.germ G.val.presheaf U z hU s) =
      ψ.val.app (op U) s ⟨hU⟩ :=
  stalkMapOfSkyscraperPresheafHom_germ R.obj z V G.val ψ.val U hU s

/-- The morphism `(skyscraperHomEquiv G).symm φ` sends a section `s` over `U ∋ z` to `φ` of the
germ of `s` at `z`. -/
@[simp]
lemma skyscraperHomEquiv_symm_app_apply
    (G : SheafOfModules.{u} ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R))
    (φ : ↑(TopCat.Presheaf.stalk G.val.presheaf z) →ₗ[↑(TopCat.Presheaf.stalk R.obj z)] ↑V)
    (U : Opens X) (hU : z ∈ U) (s : ↑(G.val.presheaf.obj (op U))) :
    ((skyscraperHomEquiv R z V G).symm φ).val.app (op U) s ⟨hU⟩ =
      φ (TopCat.Presheaf.germ G.val.presheaf U z hU s) := rfl

/-- The skyscraper at `z`, as a functor from `𝒪_{X,z}`-modules to sheaves of
`𝒪_X`-modules. -/
noncomputable def skyscraperFunctor :
    ModuleCat.{u} ↑(TopCat.Presheaf.stalk R.obj z) ⥤
      SheafOfModules.{u} ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R) where
  obj V := skyscraper R z V
  map φ := ⟨skyscraperPresheafMap R.obj z φ⟩
  map_id _ := by
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext ?_)
    exact LinearMap.ext fun g => funext fun _ => rfl
  map_comp _ _ := by
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext ?_)
    exact LinearMap.ext fun g => funext fun _ => rfl

/-- The stalk at `z` as a functor from sheaves of `𝒪_X`-modules to `𝒪_{X,z}`-modules. -/
noncomputable def stalkSheafFunctor :
    SheafOfModules.{u} ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R) ⥤
      ModuleCat.{u} ↑(TopCat.Presheaf.stalk R.obj z) :=
  SheafOfModules.forget _ ⋙ stalkPresheafFunctor R.obj z

/-- **Stacks 009C for sheaves of modules, as an adjunction.** The stalk functor at `z` on
sheaves of `𝒪_X`-modules is left adjoint to the skyscraper functor at `z`. -/
noncomputable def stalkSkyscraperAdjunction :
    stalkSheafFunctor R z ⊣ skyscraperFunctor R z :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun G V =>
        (ModuleCat.homEquiv (M := (stalkSheafFunctor R z).obj G) (N := V)).trans
          (skyscraperHomEquiv R z V G).symm
      homEquiv_naturality_left_symm := fun {G' G V} χ φ => by
        refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
        obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq G'.val.presheaf m
        refine Eq.trans
          (stalkMapOfSkyscraperPresheafHom_germ R.obj z V G'.val (χ ≫ φ).val U hU s) ?_
        exact ((congrArg (stalkMapOfSkyscraperPresheafHom R.obj z V G.val φ.val)
            (stalkLinearMap_germ χ.val U hU s)).trans
          (stalkMapOfSkyscraperPresheafHom_germ R.obj z V G.val φ.val U hU _)).symm
      homEquiv_naturality_right := fun {G V V'} φ ν => by
        refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext
          (LinearMap.ext fun s => funext fun _ => rfl)) }

end Stacks.Modules

end
