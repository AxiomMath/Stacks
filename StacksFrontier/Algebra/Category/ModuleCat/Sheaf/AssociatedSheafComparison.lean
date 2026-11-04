module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.Topology.Sheaves.Skyscraper
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ChangeOfRingsAdjunction
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
import StacksCore.Tactic.StacksAttribute

/-!
# The sheaf associated to a module and a ring map to global sections

Let `(X, 𝒪_X)` be a ringed space, let `α : R → Γ(X, 𝒪_X)` be a ring homomorphism, and let `M`
be an `R`-module. Stacks 01BH gives three constructions of the associated sheaf of
`𝒪_X`-modules `ℱ_M`: pullback along the morphism `π : X → ({*}, R)`, the cokernel of a
presentation matrix over `𝒪_X`, and the sheafification of `U ↦ 𝒪_X(U) ⊗_R M`. This file
builds the coefficient point `({*}, R)`, the morphism `π`, construction (3) together with its
universal property, and construction (1): the existence of the pullback along `π` at an arbitrary
module universe, and its identification with construction (3) applied to the sections at the
point.

## Main definitions

* `coefficientPoint` is the one-point ringed space `({*}, R)`, the skyscraper sheaf at the
  unique point of `PUnit`.
* `coefficientPointSectionsIso` identifies `R` with the global sections of its structure sheaf.
* `skyscraperDesc` builds a morphism out of a skyscraper presheaf of rings from its component
  on the whole space.
* `toCoefficientPoint` is the morphism of ringed spaces `π : X ⟶ ({*}, R)` with `π^♯ = α`.
* `constantRingPresheaf`, `globalSectionsMap`, `constantModulePresheaf` and
  `associatedPresheaf` are the ingredients of construction (3): the presheaf `U ↦ 𝒪_X(U) ⊗_R M`
  with `R` acting through `α` followed by restriction.
* `associatedSheaf` and `associatedSheafFunctor` are construction (3) itself, the
  sheafification of `associatedPresheaf`, as an object and as a functor in `M`.
* `globalSectionsFunctor` and `presheafGlobalSections` send a (pre)sheaf of `𝒪_X`-modules to its
  global sections regarded as an `R`-module along `α`.
* `coefficientRingEquiv` identifies `R` with the sections of the coefficient point's structure
  sheaf, as rings; `pointSections` is evaluation on the whole space read through it.
* `coefficientPointPullback` and `coefficientPointPresheafPullback` are construction (1): pullback
  of (pre)sheaves of modules along `π`, at an arbitrary module universe.
* `uliftTensorIso` identifies, on each open, `𝒪_X(U) ⊗_R M` with the same tensor product for `M`
  lifted to a larger universe.

## Main results

* `associatedSheafAdjunction`: construction (3) is left adjoint to global sections with scalars
  restricted along `α`, so that `Hom_{𝒪_X}(ℱ_M, 𝒢) = Hom_R(M, Γ(X, 𝒢))`.
* `associatedSheafAdjunction_unit_app_apply` and
  `presheafGlobalSectionsAdjunction_unit_app_apply` compute the unit of that adjunction, and of
  its presheaf-level half, on sections: both send `m` to `1 ⊗ m`, the first followed by
  sheafification.
* `constantModuleAdjunction` is the half of that adjunction carried by the constant presheaf.
* `evaluationTop_faithful`, `evaluationTop_full` and `pointSectionsFullyFaithful`: a presheaf of
  modules on the coefficient point is determined, together with its morphisms, by its sections on
  the whole space.
* `structureSheafHom_app_top`: the scalar map `α : R → Γ(X, 𝒪_X)` of construction (3) is the
  identification `R ≅ 𝒪_{pt}({*})` followed by `π^♯` on the whole space. Equivalently
  `globalSectionsMap_app_top_factors`.
* `pushforwardPointSectionsIso`: pushforward to the coefficient point, followed by sections on
  the whole space, is global sections with scalars restricted along `α`.
* `presheafPushforward_isRightAdjoint` and `sheafPushforward_isRightAdjoint`: pushforward along
  `π` admits a left adjoint, for an arbitrary module universe.
* `coefficientPointPullbackIsoAssociatedSheaf` is the comparison of constructions (1) and (3):
  pulling a sheaf of modules on `({*}, R)` back along `π` is construction (3) applied to its
  sections on the whole space.

## References

* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat Opposite AlgebraicGeometry
open scoped TensorProduct

universe u v

namespace Stacks.AssociatedSheaf

/-- Membership of the point in an open of the one-point space, decided classically. -/
local instance pointMemDecidable :
    ∀ U : Opens (TopCat.of PUnit.{u + 1}), Decidable (PUnit.unit ∈ U) :=
  fun _ ↦ Classical.propDecidable _

/-- An open of the one-point space containing the point is the whole space. -/
theorem eq_top_of_mem {U : Opens (TopCat.of PUnit.{u + 1})} (h : PUnit.unit ∈ U) : U = ⊤ := by
  ext x; exact iff_of_true (by cases x; exact h) trivial

/-- An open of the one-point space not containing the point is empty. -/
theorem eq_bot_of_notMem {U : Opens (TopCat.of PUnit.{u + 1})} (h : PUnit.unit ∉ U) : U = ⊥ := by
  ext x; exact iff_of_false (by cases x; exact h) (by simp)

/-- The one-point ringed space with ring `R`: the skyscraper sheaf at the unique point. -/
def coefficientPoint (R : CommRingCat.{u}) : RingedSpace.{u, u} where
  carrier := TopCat.of PUnit
  presheaf := skyscraperPresheaf PUnit.unit R
  IsSheaf := skyscraperPresheaf_isSheaf (X := TopCat.of PUnit) PUnit.unit R

/-- The structure sheaf of `coefficientPoint R` is the skyscraper presheaf with value `R`. -/
@[simp] theorem coefficientPoint_presheaf (R : CommRingCat.{u}) :
    (coefficientPoint R).presheaf =
      skyscraperPresheaf (X := TopCat.of PUnit.{u + 1}) PUnit.unit R := rfl

/-- The sections of the skyscraper presheaf on an open containing the point. -/
def skyscraperObjIso (G : CommRingCat.{u}) {U : Opens (TopCat.of PUnit.{u + 1})}
    (h : PUnit.unit ∈ U) :
    (skyscraperPresheaf (X := TopCat.of PUnit.{u + 1}) PUnit.unit G).obj (op U) ≅ G :=
  eqToIso (by rw [skyscraperPresheaf_obj, unop_op, ite_eq_left h])

/-- The canonical identification of `R` with the global sections of the structure sheaf of the
one-point ringed space. -/
def coefficientPointSectionsIso (R : CommRingCat.{u}) :
    R ≅ (coefficientPoint R).presheaf.obj (op ⊤) :=
  (skyscraperObjIso R (U := ⊤) trivial).symm

/-- A morphism out of the skyscraper presheaf on the one-point space, into a presheaf whose
sections on the empty open form a terminal object, is determined by a morphism on the whole
space. -/
def skyscraperDesc {R : CommRingCat.{u}}
    (G : TopCat.Presheaf CommRingCat.{u} (TopCat.of PUnit.{u + 1}))
    (hG : ∀ U : Opens (TopCat.of PUnit.{u + 1}), PUnit.unit ∉ U → IsTerminal (G.obj (op U)))
    (g : R ⟶ G.obj (op ⊤)) :
    skyscraperPresheaf (X := TopCat.of PUnit.{u + 1}) PUnit.unit R ⟶ G where
  app U := if h : PUnit.unit ∈ U.unop then
      (skyscraperObjIso R h).hom ≫ g ≫
        G.map (eqToHom (congrArg op (eq_top_of_mem h).symm))
    else (hG U.unop h).from _
  naturality := by
    intro U V i
    by_cases hV : PUnit.unit ∈ V.unop
    · have hU : PUnit.unit ∈ U.unop := i.unop.le hV
      obtain rfl : U = op ⊤ := Opposite.unop_injective (eq_top_of_mem hU)
      obtain rfl : V = op ⊤ := Opposite.unop_injective (eq_top_of_mem hV)
      obtain rfl : i = 𝟙 _ := Subsingleton.elim _ _
      simp only [CategoryTheory.Functor.map_id, Category.comp_id, dite_eq_left hU, eqToHom_refl]
      exact Category.id_comp _
    · exact (hG V.unop hV).hom_ext _ _

/-- On the whole space, `skyscraperDesc` is the given morphism, read through the identification
of the skyscraper's sections with the ring. -/
theorem skyscraperDesc_app_top {R : CommRingCat.{u}}
    (G : TopCat.Presheaf CommRingCat.{u} (TopCat.of PUnit.{u + 1}))
    (hG : ∀ U : Opens (TopCat.of PUnit.{u + 1}), PUnit.unit ∉ U → IsTerminal (G.obj (op U)))
    (g : R ⟶ G.obj (op ⊤)) :
    (skyscraperDesc G hG g).app (op ⊤) =
      (skyscraperObjIso R (U := ⊤) trivial).hom ≫ g := by
  simp [skyscraperDesc]

/-- The constant map from a topological space to the one-point space. -/
abbrev toPointMap (X : TopCat.{u}) : X ⟶ TopCat.of PUnit.{u + 1} :=
  TopCat.ofHom (ContinuousMap.const _ PUnit.unit)

/-- The preimage of the whole one-point space under `toPointMap X` is the whole space. -/
theorem toPointMap_obj_top (X : TopCat.{u}) : (Opens.map (toPointMap X)).obj ⊤ = ⊤ := rfl

/-- The preimage under `toPointMap X` of an open of the one-point space not containing the point
is empty. -/
theorem toPointMap_obj_eq_bot {X : TopCat.{u}} {U : Opens (TopCat.of PUnit.{u + 1})}
    (h : PUnit.unit ∉ U) : (Opens.map (toPointMap X)).obj U = ⊥ := by
  ext x; exact iff_of_false h (by simp)

/-- The morphism of ringed spaces `π : X ⟶ ({*}, R)` determined by a ring map
`α : R ⟶ Γ(X, 𝒪_X)`. -/
def toCoefficientPoint (X : RingedSpace.{u, u}) {R : CommRingCat.{u}}
    (α : R ⟶ X.presheaf.obj (op ⊤)) : X ⟶ coefficientPoint R :=
  InducedCategory.homMk
    { base := toPointMap X.carrier
      c := skyscraperDesc (R := R) (toPointMap X.carrier _* X.presheaf)
        (fun _ h ↦ X.sheaf.isTerminalOfEqEmpty (toPointMap_obj_eq_bot h)) α }

section PointModules

variable {Rc : CommRingCat.{u}}

/-- Off the point, the structure sheaf of the coefficient point is the zero ring. -/
theorem subsingleton_coefficientPoint_presheaf_obj {U : Opens (TopCat.of PUnit.{u + 1})}
    (h : PUnit.unit ∉ U) : Subsingleton ((coefficientPoint Rc).presheaf.obj (op U)) :=
  CommRingCat.subsingleton_of_isTerminal
    ((coefficientPoint Rc).sheaf.isTerminalOfEqEmpty (eq_bot_of_notMem h))

/-- A module over a ring in which `1 = 0` is zero. -/
theorem subsingleton_of_subsingleton_ring {S : Type u} [Ring S] [Subsingleton S]
    {M : Type*} [AddCommGroup M] [Module S M] : Subsingleton M :=
  Module.subsingleton S M

/-- A presheaf of modules on the coefficient point vanishes off the point: its scalars there
form the zero ring. -/
theorem subsingleton_obj_of_notMem
    (N : PresheafOfModules.{v}
      (structureSheafRing (coefficientPoint Rc)).obj)
    {U : Opens (TopCat.of PUnit.{u + 1})} (h : PUnit.unit ∉ U) :
    Subsingleton (N.obj (op U)) :=
  have : Subsingleton
      ((structureSheafRing (coefficientPoint Rc)).obj.obj (op U)) :=
    subsingleton_coefficientPoint_presheaf_obj h
  subsingleton_of_subsingleton_ring
    (S := (structureSheafRing (coefficientPoint Rc)).obj.obj (op U))

/-- Evaluation on the whole space, from presheaves of modules on the coefficient point. -/
abbrev evaluationTop :
    PresheafOfModules.{v} (structureSheafRing (coefficientPoint Rc)).obj ⥤
      ModuleCat.{v}
        ((structureSheafRing (coefficientPoint Rc)).obj.obj (op ⊤)) :=
  PresheafOfModules.evaluation _ (op ⊤)

/-- A morphism of presheaves of modules on the coefficient point is determined by its component
on the whole space. -/
theorem hom_ext_of_app_top
    {N G : PresheafOfModules.{v}
      (structureSheafRing (coefficientPoint Rc)).obj}
    {f g : N ⟶ G} (h : f.app (op ⊤) = g.app (op ⊤)) : f = g := by
  refine PresheafOfModules.hom_ext fun U ↦ ?_
  by_cases hU : PUnit.unit ∈ U.unop
  · obtain rfl : U = op ⊤ := Opposite.unop_injective (eq_top_of_mem hU)
    exact h
  · exact ModuleCat.hom_ext (LinearMap.ext fun _ ↦ (subsingleton_obj_of_notMem G hU).elim _ _)

/-- Evaluation on the whole space is faithful on presheaves of modules on the coefficient
point. -/
instance evaluationTop_faithful :
    (evaluationTop.{u, v} (Rc := Rc)).Faithful where
  map_injective h := hom_ext_of_app_top h

/-- Evaluation on the whole space is full on presheaves of modules on the coefficient point. -/
instance evaluationTop_full : (evaluationTop.{u, v} (Rc := Rc)).Full where
  map_surjective {N G} h := by
    classical
    let app : ∀ U, N.obj U ⟶ G.obj U := fun U ↦
      if hU : PUnit.unit ∈ U.unop then
        (Opposite.unop_injective (eq_top_of_mem hU) : U = op ⊤) ▸ h
      else 0
    have happ : app (op ⊤) = h :=
      dite_eq_left (show PUnit.unit ∈ (op (⊤ : Opens (TopCat.of PUnit.{u + 1}))).unop from trivial)
    refine ⟨⟨app, fun {U V} i ↦ ?_⟩, happ⟩
    by_cases hV : PUnit.unit ∈ V.unop
    · have hU : PUnit.unit ∈ U.unop := i.unop.le hV
      obtain rfl : U = op ⊤ := Opposite.unop_injective (eq_top_of_mem hU)
      obtain rfl : V = op ⊤ := Opposite.unop_injective (eq_top_of_mem hV)
      obtain rfl : i = 𝟙 _ := Subsingleton.elim _ _
      rw [happ]
      simp only [PresheafOfModules.map_id]
      exact ((ModuleCat.restrictScalarsId' _ _).inv.naturality h).symm
    · exact ModuleCat.hom_ext
        (LinearMap.ext fun _ ↦ (subsingleton_obj_of_notMem G hV).elim _ _)

end PointModules

section Scaffolding

variable (X : RingedSpace.{u, u})

/-- Sheafification of presheaves of abelian groups exists on the open-cover site of a ringed
space in any universe containing the space's own. -/
theorem hasModuleSheafify : HasSheafify (Opens.grothendieckTopology X.carrier)
    AddCommGrpCat.{max u v} :=
  hasSheafifyEssentiallySmallSite.{_, _, _, _, max u v} _ _

/-- Weak equivalences of presheaves of abelian groups on the open-cover site of a ringed space
are the locally bijective maps, in any universe containing the space's own. -/
theorem moduleSheafifyWEqualsLocallyBijective :
    (Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{max u v} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{_, _, _, _, max u v} _

/-- The constant presheaf of commutative rings with value `R` on a ringed space. -/
abbrev constantRingPresheaf (R : Type u) [CommRing R] : TopCat.Presheaf CommRingCat X.carrier :=
  (Functor.const _).obj (CommRingCat.of R)

/-- The map from the constant presheaf `R` to the structure sheaf induced by a ring map from `R`
to the global sections: the given map followed by restriction from `X` to `U`. -/
@[simps]
def globalSectionsMap {R : Type u} [CommRing R] (α : R →+* X.presheaf.obj (op ⊤)) :
    constantRingPresheaf X R ⟶ X.presheaf where
  app U := CommRingCat.ofHom ((X.presheaf.map (homOfLE le_top).op).hom.comp α)
  naturality {U V} f := by
    ext r
    change (X.presheaf.map (homOfLE le_top).op).hom (α r) =
      (X.presheaf.map f).hom ((X.presheaf.map (homOfLE le_top).op).hom (α r))
    rw [← CategoryTheory.comp_apply, ← X.presheaf.map_comp]
    congr

/-- The constant presheaf of modules with value `M`, over the constant presheaf of rings `R`. -/
@[simps obj]
def constantModulePresheaf {R : Type u} [CommRing R] (M : ModuleCat.{v} R) :
    PresheafOfModules.{v} (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf (constantRingPresheaf
      X R)) where
  obj _ := M
  map {U V} f :=
    (ModuleCat.restrictScalarsId'
      ((Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf (constantRingPresheaf X R)).map f).hom
        rfl).inv.app M
  map_id _ := by simp
  map_comp _ _ := ModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl)

/-- The presheaf `U ↦ 𝒪_X(U) ⊗_R M`, with `R` acting on `𝒪_X(U)` through `α` followed by
restriction of global sections to `U`. -/
abbrev associatedPresheaf {R : Type u} [CommRing R] (α : R →+* X.presheaf.obj (op ⊤))
    (M : ModuleCat.{v} R) :
    PresheafOfModules.{max u v} (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf X.presheaf) :=
  (Stacks.PresheafOfModules.ChangeOfRings.changeOfRings (globalSectionsMap X α)).obj
    (constantModulePresheaf X M)

/-- The sheaf of `𝒪_X`-modules associated to a module `M` and a ring map `α : R → Γ(X, 𝒪_X)`:
the sheafification of `U ↦ 𝒪_X(U) ⊗_R M`. -/
abbrev associatedSheaf {R : Type u} [CommRing R] (α : R →+* X.presheaf.obj (op ⊤))
    (M : ModuleCat.{v} R) :
    SheafOfModules.{max u v} (structureSheafRing X) := by
  letI := hasModuleSheafify.{u, v} X
  letI := moduleSheafifyWEqualsLocallyBijective.{u, v} X
  exact (PresheafOfModules.sheafification.{max u v}
    (R := structureSheafRing X)
    (𝟙 (structureSheafRing X).obj)).obj (associatedPresheaf X α M)

/-- The constant presheaf-of-modules functor, on modules of an arbitrary universe. -/
@[simps]
def constantModuleFunctor {R : Type u} [CommRing R] : ModuleCat.{v} R ⥤
    PresheafOfModules.{v} (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf (constantRingPresheaf
      X R)) where
  obj M := constantModulePresheaf X M
  map f := { app := fun _ ↦ ModuleCat.ofHom f.hom, naturality := by intros; ext m; rfl }
  map_id M := by ext U m; rfl
  map_comp f g := by ext U m; rfl

/-- Morphisms out of a constant presheaf of modules are determined by their component on the
whole space. -/
@[simps]
def constantModuleHomEquiv {R : Type u} [CommRing R] (M : ModuleCat.{v} R)
    (N : PresheafOfModules.{v} (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf
      (constantRingPresheaf X R))) :
    ((constantModuleFunctor X).obj M ⟶ N) ≃ (M ⟶ N.obj (op ⊤)) where
  toFun f := ModuleCat.ofHom (f.app (op ⊤)).hom
  invFun f :=
    { app := fun U ↦ ModuleCat.ofHom
        { toFun := fun m ↦ N.map (homOfLE le_top).op (f m)
          map_add' x y := by
            rw [f.hom.map_add]
            exact (N.map _).hom.map_add _ _
          map_smul' r m := by
            change N.map _ (f (r • m)) = r • N.map _ (f m)
            rw [f.hom.map_smul, N.map_smul]
            rfl }
      naturality _ := by
        ext m
        exact N.map_comp_apply (homOfLE le_top).op _ (f m) }
  left_inv f := by
    ext U m
    exact (PresheafOfModules.naturality_apply f
      (homOfLE (show U.unop ≤ ⊤ from le_top)).op m).symm
  right_inv f := by
    ext m
    change N.map (𝟙 (op ⊤)) (f m) = f m
    rw [N.map_id]
    rfl

/-- The constant presheaf-of-modules functor is left adjoint to evaluation on the whole
space. -/
def constantModuleAdjunction {R : Type u} [CommRing R] :
    constantModuleFunctor.{u, v} X ⊣ PresheafOfModules.evaluation
      (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf (constantRingPresheaf X R)) (op ⊤) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := constantModuleHomEquiv X
      homEquiv_naturality_left_symm := by intros; ext U m; rfl
      homEquiv_naturality_right := by intros; ext m; rfl }

variable {R : Type u} [CommRing R] (α : R →+* X.presheaf.obj (op ⊤))

/-- The sheafification of `U ↦ 𝒪_X(U) ⊗_R M`, as a functor of the `R`-module `M`. -/
abbrev associatedSheafFunctor : ModuleCat.{v} R ⥤
    SheafOfModules.{max u v} (structureSheafRing X) := by
  letI := hasModuleSheafify.{u, v} X
  letI := moduleSheafifyWEqualsLocallyBijective.{u, v} X
  let F := PresheafOfModules.sheafification.{max u v}
    (R := structureSheafRing X)
    (𝟙 (structureSheafRing X).obj)
  exact constantModuleFunctor X ⋙ Stacks.PresheafOfModules.ChangeOfRings.changeOfRings
    (globalSectionsMap X α) ⋙ F

/-- Global sections of a sheaf of modules, with scalars restricted along `α`. -/
abbrev globalSectionsFunctor :
    SheafOfModules.{max u v} (structureSheafRing X) ⥤ ModuleCat.{max u v} R :=
  (SheafOfModules.forget (structureSheafRing X) ⋙
    PresheafOfModules.restrictScalars (𝟙 (structureSheafRing X).obj)) ⋙
  Stacks.PresheafOfModules.ChangeOfRings.restrictScalars (globalSectionsMap X α) ⋙
  PresheafOfModules.evaluation (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf
    (constantRingPresheaf X R)) (op ⊤)

/-- The tensor-sheafification adjunction: `associatedSheafFunctor` is left adjoint to global
sections with scalars restricted along `α`, so that `Mor_{𝒪_X}(ℱ_M, 𝒢) = Hom_R(M, Γ(X, 𝒢))`. -/
@[stacks 01BH "Mor(ℱ_M, 𝒢) = Hom_R(M, Γ(X,𝒢))"]
def associatedSheafAdjunction :
    associatedSheafFunctor.{u, max u v} X α ⊣ globalSectionsFunctor.{u, v} X α :=
  letI := hasModuleSheafify.{u, v} X
  letI := moduleSheafifyWEqualsLocallyBijective.{u, v} X
  ((constantModuleAdjunction X).comp
    (Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsAdjunction (globalSectionsMap X α))).comp
    (PresheafOfModules.sheafificationAdjunction.{max u v}
      (R := structureSheafRing X)
      (𝟙 (structureSheafRing X).obj))

/-- The unit `M ⟶ Γ(X, ℱ_M)` of `associatedSheafAdjunction` sends `m` to the image of
`1 ⊗ m ∈ 𝒪_X(X) ⊗_R M` under the sheafification map of `U ↦ 𝒪_X(U) ⊗_R M`. -/
theorem associatedSheafAdjunction_unit_app_apply (M : ModuleCat.{max u v} R) (m : M) :
    letI := hasModuleSheafify.{u, v} X
    letI := moduleSheafifyWEqualsLocallyBijective.{u, v} X
    letI := ((globalSectionsMap X α).app (op ⊤)).hom.toAlgebra
    ((associatedSheafAdjunction.{u, v} X α).unit.app M).hom m =
      (((PresheafOfModules.sheafificationAdjunction.{max u v}
            (R := structureSheafRing X)
            (𝟙 (structureSheafRing X).obj)).unit.app
          (associatedPresheaf X α M)).app (op ⊤)).hom
        ((1 : X.presheaf.obj (op ⊤)) ⊗ₜ[(constantRingPresheaf X R).obj (op ⊤)] m) :=
  rfl

end Scaffolding

section Comparison

variable (X : RingedSpace.{u, u}) {R : Type u} [CommRing R] (α : R →+* X.presheaf.obj (op ⊤))

/-- The morphism of ringed spaces `π : X ⟶ ({*}, R)` attached to `α`. -/
abbrev toCoefficientPoint' : X ⟶ coefficientPoint (CommRingCat.of R) :=
  toCoefficientPoint X (CommRingCat.ofHom α)

/-- The component of `π^♯` on the whole space, read through the identification of `R` with the
sections of the coefficient point's structure sheaf, is `α`. -/
theorem structureSheafHom_app_top :
    (forget₂ CommRingCat.{u} RingCat.{u}).map
        (coefficientPointSectionsIso (CommRingCat.of R)).hom ≫
      (RingedSpaceModuleAdjunction.structureSheafHom
        (toCoefficientPoint' X α)).hom.app (op ⊤) =
    (forget₂ CommRingCat.{u} RingCat.{u}).map (CommRingCat.ofHom α) := by
  have hc := skyscraperDesc_app_top (R := CommRingCat.of R)
    (toPointMap X.carrier _* X.presheaf)
    (fun _ h ↦ X.sheaf.isTerminalOfEqEmpty (toPointMap_obj_eq_bot h)) (CommRingCat.ofHom α)
  have key : (RingedSpaceModuleAdjunction.structureSheafHom
        (toCoefficientPoint' X α)).hom.app (op ⊤) =
      (forget₂ CommRingCat.{u} RingCat.{u}).map
        ((skyscraperObjIso (CommRingCat.of R) (U := ⊤) trivial).hom ≫ CommRingCat.ofHom α) :=
    congrArg (fun g ↦ (forget₂ CommRingCat.{u} RingCat.{u}).map g) hc
  rw [key, coefficientPointSectionsIso, Iso.symm_hom]
  exact ((forget₂ CommRingCat.{u} RingCat.{u}).map_comp _ _).symm.trans
    (congrArg (forget₂ CommRingCat.{u} RingCat.{u}).map
      (Iso.inv_hom_id_assoc _ (CommRingCat.ofHom α)))

/-- Elementwise form of `structureSheafHom_app_top`. -/
theorem structureSheafHom_app_top_apply (r : R) :
    ((RingedSpaceModuleAdjunction.structureSheafHom
        (toCoefficientPoint' X α)).hom.app (op ⊤)).hom
      (((forget₂ CommRingCat.{u} RingCat.{u}).map
        (coefficientPointSectionsIso (CommRingCat.of R)).hom).hom r) = α r :=
  DFunLike.congr_fun (congrArg RingCat.Hom.hom (structureSheafHom_app_top X α)) r

/-- `R`, identified as a ring with the sections of the coefficient point's structure sheaf on the
whole space. -/
def coefficientRingEquiv : RingCat.of R ≃+*
    (structureSheafRing
      (coefficientPoint (CommRingCat.of R))).obj.obj (op ⊤) :=
  ((forget₂ CommRingCat.{u} RingCat.{u}).mapIso
    (coefficientPointSectionsIso (CommRingCat.of R))).ringCatIsoToRingEquiv

/-- Evaluation on the whole space, with the scalars read through `R`: a presheaf of modules on
the coefficient point, regarded as an `R`-module. -/
abbrev pointSections : PresheafOfModules.{v}
      (structureSheafRing (coefficientPoint (CommRingCat.of R))).obj ⥤
    ModuleCat.{v} R :=
  evaluationTop ⋙ ModuleCat.restrictScalars (coefficientRingEquiv (R := R)).toRingHom

/-- `pointSections` is fully faithful: a presheaf of modules on the coefficient point, and its
morphisms, are determined by its sections on the whole space. -/
def pointSectionsFullyFaithful : (pointSections.{u, v} (R := R)).FullyFaithful :=
  (Functor.FullyFaithful.ofFullyFaithful
      (evaluationTop.{u, v} (Rc := CommRingCat.of R))).comp
    (Functor.FullyFaithful.ofFullyFaithful _)

/-- The component of `π^♯` on the whole space. -/
abbrev pointStructureMap :
    (structureSheafRing
        (coefficientPoint (CommRingCat.of R))).obj.obj (op ⊤) ⟶
      ((RingedSpaceModuleAdjunction.opensMap
        (toCoefficientPoint' X α)).op ⋙
          (structureSheafRing X).obj).obj (op ⊤) :=
  (RingedSpaceModuleAdjunction.structureSheafHom (toCoefficientPoint' X α)).hom.app (op ⊤)

/-- On the whole space, `globalSectionsMap X α` is `α`. -/
theorem globalSectionsMap_app_top_apply (r : R) :
    ((globalSectionsMap X α).app (op ⊤)).hom r = α r := by
  rw [globalSectionsMap_app]
  change (X.presheaf.map (homOfLE le_top).op).hom (α r) = α r
  rw [Subsingleton.elim (homOfLE (show (op (⊤ : Opens X.carrier)).unop ≤ ⊤ from le_top)).op
    (𝟙 (op (⊤ : Opens X.carrier))), X.presheaf.map_id]
  rfl

/-- The scalar map `R → Γ(X, 𝒪_X)` used by construction (3) factors through the coefficient
point: it is the identification `R ≅ 𝒪_{pt}({*})` followed by `π^♯` on the whole space. -/
theorem globalSectionsMap_app_top_factors :
    ((globalSectionsMap X α).app (op ⊤)).hom =
      (pointStructureMap X α).hom.comp (coefficientRingEquiv (R := R)).toRingHom :=
  RingHom.ext fun r ↦ by
    rw [globalSectionsMap_app_top_apply]
    exact (structureSheafHom_app_top_apply X α r).symm

/-- Global sections of a *presheaf* of `𝒪_X`-modules, with scalars restricted along `α`. -/
abbrev presheafGlobalSections : PresheafOfModules.{max u v}
      (structureSheafRing X).obj ⥤ ModuleCat.{max u v} R :=
  Stacks.PresheafOfModules.ChangeOfRings.restrictScalars (globalSectionsMap X α) ⋙
    PresheafOfModules.evaluation (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf
      (constantRingPresheaf X R)) (op ⊤)

/-- The presheaf-level tensor adjunction: `U ↦ 𝒪_X(U) ⊗_R M` is left adjoint to global sections
with scalars restricted along `α`. -/
def presheafGlobalSectionsAdjunction :
    constantModuleFunctor.{u, max u v} X ⋙
        Stacks.PresheafOfModules.ChangeOfRings.changeOfRings (globalSectionsMap X α) ⊣
      presheafGlobalSections.{u, v} X α :=
  (constantModuleAdjunction X).comp
    (Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsAdjunction (globalSectionsMap X α))

/-- The unit `M ⟶ 𝒪_X(X) ⊗_R M` of `presheafGlobalSectionsAdjunction` on sections sends `m` to
`1 ⊗ m`. -/
theorem presheafGlobalSectionsAdjunction_unit_app_apply (M : ModuleCat.{max u v} R) (m : M) :
    letI := ((globalSectionsMap X α).app (op ⊤)).hom.toAlgebra
    ((presheafGlobalSectionsAdjunction.{u, v} X α).unit.app M).hom m =
      (1 : X.presheaf.obj (op ⊤)) ⊗ₜ[(constantRingPresheaf X R).obj (op ⊤)] m :=
  rfl

/-- Pushforward to the coefficient point, followed by sections on the whole space, is global
sections with scalars restricted along `α`. -/
def pushforwardPointSectionsIso :
    PresheafOfModules.pushforward.{max u v}
        (RingedSpaceModuleAdjunction.structureSheafHom (toCoefficientPoint' X α)).hom ⋙
      pointSections.{u, max u v} (R := R) ≅ presheafGlobalSections.{u, v} X α :=
  NatIso.ofComponents
    (fun M ↦ (ModuleCat.restrictScalarsComp'App
      (coefficientRingEquiv (R := R)).toRingHom (pointStructureMap X α).hom
      ((globalSectionsMap X α).app (op ⊤)).hom
      (globalSectionsMap_app_top_factors X α) (M.obj (op ⊤))).symm)
    (fun _ ↦ ModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl))

/-- Pushforward of presheaves of modules along `π : X ⟶ ({*}, R)` admits a left adjoint, for an
arbitrary module universe. -/
instance presheafPushforward_isRightAdjoint :
    (PresheafOfModules.pushforward.{max u v}
      (RingedSpaceModuleAdjunction.structureSheafHom
        (toCoefficientPoint' X α)).hom).IsRightAdjoint :=
  (Adjunction.restrictFullyFaithful
    (L := pointSections.{u, max u v} (R := R) ⋙ constantModuleFunctor.{u, max u v} X ⋙
      Stacks.PresheafOfModules.ChangeOfRings.changeOfRings (globalSectionsMap X α))
    (R := PresheafOfModules.pushforward.{max u v}
      (RingedSpaceModuleAdjunction.structureSheafHom (toCoefficientPoint' X α)).hom)
    (presheafGlobalSectionsAdjunction.{u, v} X α)
    (pointSectionsFullyFaithful (R := R)) (Functor.FullyFaithful.id _)
    (Functor.rightUnitor _).symm
    (Functor.leftUnitor _ ≪≫ (pushforwardPointSectionsIso.{u, v} X α).symm)).isRightAdjoint

/-- Pushforward of sheaves of modules along `π : X ⟶ ({*}, R)` admits a left adjoint, for an
arbitrary module universe. -/
theorem sheafPushforward_isRightAdjoint :
    (SheafOfModules.pushforward.{max u v}
      (RingedSpaceModuleAdjunction.structureSheafHom
        (toCoefficientPoint' X α))).IsRightAdjoint :=
  let := hasModuleSheafify.{u, v} X
  let := moduleSheafifyWEqualsLocallyBijective.{u, v} X
  SheafOfModules.instIsRightAdjointPushforward _

/-- Pullback of sheaves of modules along `π : X ⟶ ({*}, R)`, at an arbitrary module
universe. -/
def coefficientPointPullback :
    SheafOfModules.{max u v}
        (structureSheafRing (coefficientPoint (CommRingCat.of R))) ⥤
      SheafOfModules.{max u v} (structureSheafRing X) :=
  letI := sheafPushforward_isRightAdjoint.{u, v} X α
  SheafOfModules.pullback.{max u v}
    (RingedSpaceModuleAdjunction.structureSheafHom (toCoefficientPoint' X α))

/-- The adjunction `π^* ⊣ π_*` for the coefficient-point morphism, at an arbitrary module
universe. -/
def coefficientPointAdjunction :
    coefficientPointPullback.{u, v} X α ⊣
      SheafOfModules.pushforward.{max u v}
        (RingedSpaceModuleAdjunction.structureSheafHom (toCoefficientPoint' X α)) :=
  letI := sheafPushforward_isRightAdjoint.{u, v} X α
  SheafOfModules.pullbackPushforwardAdjunction
    (RingedSpaceModuleAdjunction.structureSheafHom (toCoefficientPoint' X α))

/-- The presheaf-level pullback along `π`, at an arbitrary module universe. -/
def coefficientPointPresheafPullback :
    PresheafOfModules.{max u v}
        (structureSheafRing
          (coefficientPoint (CommRingCat.of R))).obj ⥤
      PresheafOfModules.{max u v} (structureSheafRing X).obj :=
  letI := presheafPushforward_isRightAdjoint.{u, v} X α
  PresheafOfModules.pullback.{max u v}
    (RingedSpaceModuleAdjunction.structureSheafHom (toCoefficientPoint' X α)).hom

/-- The presheaf-level pullback along `π` is the sections on the whole space followed by
construction (3) without sheafification. -/
def coefficientPointPresheafPullbackIso :
    coefficientPointPresheafPullback.{u, v} X α ≅
      pointSections.{u, max u v} (R := R) ⋙ constantModuleFunctor.{u, max u v} X ⋙
        Stacks.PresheafOfModules.ChangeOfRings.changeOfRings (globalSectionsMap X α) :=
  letI := presheafPushforward_isRightAdjoint.{u, v} X α
  Adjunction.leftAdjointUniq
    (PresheafOfModules.pullbackPushforwardAdjunction
      (RingedSpaceModuleAdjunction.structureSheafHom (toCoefficientPoint' X α)).hom)
    (Adjunction.restrictFullyFaithful
      (L := pointSections.{u, max u v} (R := R) ⋙ constantModuleFunctor.{u, max u v} X ⋙
        Stacks.PresheafOfModules.ChangeOfRings.changeOfRings (globalSectionsMap X α))
      (R := PresheafOfModules.pushforward.{max u v}
        (RingedSpaceModuleAdjunction.structureSheafHom (toCoefficientPoint' X α)).hom)
      (presheafGlobalSectionsAdjunction.{u, v} X α)
      (pointSectionsFullyFaithful (R := R)) (Functor.FullyFaithful.id _)
      (Functor.rightUnitor _).symm
      (Functor.leftUnitor _ ≪≫ (pushforwardPointSectionsIso.{u, v} X α).symm))

/-- Pulling a sheaf of modules on the coefficient point back along `π` is the presheaf-level
pullback of its underlying presheaf, followed by sheafification. -/
def coefficientPointPullbackIso :
    coefficientPointPullback.{u, v} X α ≅
      SheafOfModules.forget _ ⋙
        (coefficientPointPresheafPullback.{u, v} X α ⋙
          (letI := hasModuleSheafify.{u, v} X
           letI := moduleSheafifyWEqualsLocallyBijective.{u, v} X
           PresheafOfModules.sheafification.{max u v}
             (R := structureSheafRing X)
             (𝟙 (structureSheafRing X).obj))) :=
  letI := hasModuleSheafify.{u, v} X
  letI := moduleSheafifyWEqualsLocallyBijective.{u, v} X
  letI := presheafPushforward_isRightAdjoint.{u, v} X α
  SheafOfModules.pullbackIso
    (RingedSpaceModuleAdjunction.structureSheafHom (toCoefficientPoint' X α))

/-- Pulling a sheaf of modules on the coefficient point back along `π : X ⟶ ({*}, R)` is taking
its sections on the whole space as an `R`-module and then applying `associatedSheafFunctor`. -/
def coefficientPointPullbackIsoAssociatedSheaf :
    coefficientPointPullback.{u, v} X α ≅
      SheafOfModules.forget _ ⋙ pointSections.{u, max u v} (R := R) ⋙
        associatedSheafFunctor.{u, max u v} X α :=
  coefficientPointPullbackIso.{u, v} X α ≪≫
    Functor.isoWhiskerLeft (SheafOfModules.forget _)
      (Functor.isoWhiskerRight (coefficientPointPresheafPullbackIso.{u, v} X α) _)

section ULiftBridge

/-- On each open `U`, lifting the module universe of `M` does not change `𝒪_X(U) ⊗_R M`. -/
def uliftTensorIso (M : ModuleCat.{v} R) (U : (Opens X.carrier)ᵒᵖ) :
    Stacks.PresheafOfModules.ChangeOfRings.cofObj (globalSectionsMap X α)
        ((constantModuleFunctor.{u, max u v} X).obj
          (ModuleCat.of R (ULift.{u} M.carrier))) U ≅
      Stacks.PresheafOfModules.ChangeOfRings.cofObj (globalSectionsMap X α)
        ((constantModuleFunctor.{u, v} X).obj M) U :=
  letI := ((globalSectionsMap X α).app U).hom.toAlgebra
  LinearEquiv.toModuleIso
    (TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl (X.presheaf.obj U) (X.presheaf.obj U))
      (ULift.moduleEquiv (R := R) (M := M.carrier)))

/-- The restriction maps of the constant presheaf of modules with value `M` are the identity. -/
theorem constantModuleFunctor_obj_map_apply (M : ModuleCat.{v} R)
    {U V : (Opens X.carrier)ᵒᵖ} (f : U ⟶ V) (m : M) :
    ((constantModuleFunctor.{u, v} X).obj M).map f m = m := rfl

end ULiftBridge

end Comparison

end Stacks.AssociatedSheaf

end
