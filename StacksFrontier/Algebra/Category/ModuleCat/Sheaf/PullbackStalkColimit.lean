module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import StacksFrontier.Topology.Sheaves.Skyscraper.Modules
public import StacksCore.Tactic.StacksAttribute

/-!
# The stalk of a pullback of sheaves of modules

Let `f : X ⟶ Y` be a morphism of ringed spaces (in the application, of schemes) and let `N` be
a sheaf of `𝒪_Y`-modules.  The stalk of the pullback `f^*N` at a point `x` of `X` is

`(f^*N)_x = 𝒪_{X,x} ⊗_{𝒪_{Y,f x}} N_{f x}`.

Mathlib defines `SheafOfModules.pullback` as the left adjoint `(pushforward φ).leftAdjoint`,
so it offers no description of its sections and no formula for its stalks.  This file builds
the ingredient from which that formula follows **formally**: the *module skyscraper*, right
adjoint to the stalk functor on presheaves and on sheaves of modules.  With both adjunctions
in hand, the two composites

`pullback f ⋙ stalk_x ⊣ sky_x ⋙ pushforward f` and
`stalk_{f x} ⋙ extendScalars (f^♯_x) ⊣ restrictScalars (f^♯_x) ⋙ sky_{f x}`

have *isomorphic* right adjoints — in fact the comparison is a reindexing of sections along
`x ∈ f⁻¹V ↔ f x ∈ V` — so conjugation of adjoints identifies the left adjoints, which is the
stalk formula.  Nothing about tensor products, filtered colimits or colimit interchange
enters.

The name of this file records the route that was expected when it was opened — the sections of
`PresheafOfModules.pullback` as a filtered colimit, followed by a colimit interchange.  That
route also works, and is harder: the interchange needed is
`colim_j (A_j ⊗_{B_j} M_j) ≅ (colim A) ⊗_{colim B} (colim M)` over a filtered index category
with *varying* base ring, which is not in Mathlib and which the skyscraper argument below does
not need at all.

## Main definitions

* `Stacks.ModuleSkyscraper.skyAb`: the presheaf of abelian groups
  `U ↦ (PLift (x ∈ U) → A)`, which is the skyscraper at `x` with value `A` written without a
  case distinction: over an open containing `x` the index type is a singleton and the sections
  are `A`, over an open missing `x` it is empty and the sections are the zero group.
* `Stacks.ModuleSkyscraper.skyPresheaf` and `Stacks.ModuleSkyscraper.skyPresheafFunctor`: the
  same presheaf read as a presheaf of `R`-modules, a section of `R` acting through its germ at
  `x`, and the functor it defines; `Stacks.ModuleSkyscraper.skyModules` and
  `Stacks.ModuleSkyscraper.skyModulesFunctor` are the corresponding sheaf of `𝒪_X`-modules on
  a scheme and its functor.
* `Stacks.ModuleSkyscraper.stalkObj` and `Stacks.ModuleSkyscraper.stalkMapLinear`: the stalk
  of a presheaf of modules as a module over the stalk of `R`, and the linear map it induces on
  a morphism; `Stacks.ModuleSkyscraper.presheafStalkFunctor` and
  `Stacks.ModuleSkyscraper.modulesStalkFunctor` are the stalk functors on presheaves of
  modules and on `𝒪_X`-modules.
* `Stacks.ModuleSkyscraper.homEquivSky`: the hom bijection
  `(M_x ⟶ A) ≃ (M ⟶ sky_x A)`, built from `Stacks.ModuleSkyscraper.toSky` and
  `Stacks.ModuleSkyscraper.fromStalkLinear`.

## Main results

* `Stacks.ModuleSkyscraper.skyAb_isSheaf`: the skyscraper is a sheaf, by the unique-gluing
  criterion: a compatible family of sections over a cover of `U` is a family of functions on
  singleton-or-empty index types that agree at `x`, and the glued section is the value of any
  member whose open contains `x`.
* `Stacks.ModuleSkyscraper.stalkSkyAdjunction` and
  `Stacks.ModuleSkyscraper.modulesStalkSkyAdjunction`: **the stalk functor is left adjoint to
  the skyscraper functor**, on presheaves of modules over a presheaf of commutative rings on a
  space, and on sheaves of modules on a scheme.
* `Stacks.ModuleSkyscraper.pushSkyObjIso` and `Stacks.ModuleSkyscraper.pushSkyIso`: the
  pushforward of the skyscraper at `x` is the skyscraper at `f x`, with its value read over
  `𝒪_{Y,f x}` along the stalk map of `f`.  The content is the germ compatibility
  `AlgebraicGeometry.Scheme.Hom.germ_stalkMap_apply`; the underlying map of sections is a
  reindexing along `x ∈ f⁻¹V ↔ f x ∈ V`.
* `Stacks.ModuleSkyscraper.pullbackStalkIso`, `pullbackStalkObjIso` and
  `pullbackStalkLinearEquiv`: **the stalk formula**
  `(f^*N)_x ≅ 𝒪_{X,x} ⊗_{𝒪_{Y,f x}} N_{f x}` for Mathlib's `Scheme.Modules.pullback`,
  naturally in `N`, as a natural isomorphism of functors, on an object, and as an
  `𝒪_{X,x}`-linear equivalence.  This is the content of Stacks 0098; see the note on the tag
  at `pullbackStalkIso`.

## Implementation notes

The skyscraper is written `U ↦ (PLift (x ∈ U) → A)` rather than
`if x ∈ U then A else 0`.  Both describe the same presheaf, but the second is a `dite` whose
type depends on the decision, so every restriction map, every module axiom and every
naturality square splits into four cases; in the first spelling the restriction maps are
precomposition with an implication between propositions, `map_id` and `map_comp` hold by
`rfl` (structure eta for `PLift` together with proof irrelevance), and the module axioms are
pointwise.  The scalar action is `(r • g) p = R.germ U x p.down r • g p`: the germ map needs
the membership proof, and the index `p` carries it.

Every statement is made for `R : X.Presheaf CommRingCat.{u}` with modules over
`R ⋙ forget₂ CommRingCat RingCat`, because that is the shape a scheme supplies
(`X.ringCatSheaf.obj = X.presheaf ⋙ forget₂ CommRingCat RingCat` holds by `rfl`) and because
the scalars of the stalk are then the `CommRingCat`-valued stalk `R.stalk x`, which is the
ring `AlgebraicGeometry.Scheme.Modules.IsAssociatedPoint` and
`ModuleCat.extendScalars` are stated for.  Taking `R` in `RingCat` instead would force a
transport along the comparison of the `RingCat`- and `CommRingCat`-valued stalks at every
step.

**Overlap with `StacksFrontier.Topology.Sheaves.Modules.Colimits`, and why it is not removed
here.**  That file already has `AlgebraicGeometry.SheafOfModules.stalkObj`, `stalkMap`,
`stalkFunctor` and `germ_hom_smul`, so `stalkObj`, `stalkMapLinear`, `modulesStalkFunctor` and
`germ_smul'` below are a second copy of that material — but over the *other* stalk.  Its
functor is valued in `ModuleCat (TopCat.Presheaf.stalk (C := RingCat) O.obj x)`, the
`RingCat`-valued stalk of the ring sheaf; this one is valued in `ModuleCat ↑(R.stalk x)`, the
`CommRingCat`-valued stalk.  The distinction is load-bearing and not cosmetic:
`ModuleCat.extendScalars` exists only for commutative rings, and
`AlgebraicGeometry.Scheme.Modules.IsAssociatedPoint` is stated over `X.presheaf.stalk x`, so
the stalk formula below can only be assembled over the `CommRingCat` stalk.  Unifying the two
means transporting the whole development along the comparison of the two stalks, which is a
refactor of both files rather than a change to this one; it is recorded here so the choice is
visible rather than silent.

Universes are not narrowed, but they are not independent either, and that is forced rather
than chosen: `TopCat.Presheaf.pullback` makes the hom universe of the target category equal
to the universe of the space, and `PresheafOfModules.ModuleColimit` — which computes the
module structure on a stalk — ties the module and smallness universes to the ring universe.
So a single `u` carries the space, the rings and the module sections, which is exactly the
range of `Scheme.{u}`.

**The presheaf-level development lives in `StacksFrontier.Topology.Sheaves.Skyscraper.Modules`.**
That file builds the same skyscraper over the same `CommRingCat`-valued stalk, and the names
in this section — `skyAb`, `skyAb_isSheaf`, `skyModule`, `skyPresheaf`, `stalkMapLinear`,
`presheafStalkFunctor`, `skyPresheafFunctor`, `toSky`, `fromStalkLinear`, `homEquivSky`,
`stalkSkyAdjunction` — are thin wrappers around `Stacks.Modules.skyscraperAbPresheaf`,
`skyscraperAbPresheaf_isSheaf`, `skyscraperModuleSections`, `skyscraperPresheaf`,
`stalkLinearMap`, `stalkPresheafFunctor`, `skyscraperPresheafFunctor`, `skyscraperPresheafHom`,
`stalkMapOfSkyscraperPresheafHom`, `skyscraperPresheafHomEquiv` and
`stalkSkyscraperPresheafAdjunction`.  They are kept as names, rather than removed in favour of
the originals, because `skyModule` is a *global* instance here whereas the sections instance
there is registered only locally, and because the scheme-level material below — the pushforward
of a skyscraper and the stalk formula — reads the wrappers definitionally.  Everything from
`skyModules` onwards is this file's own.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 0095](https://stacks.math.columbia.edu/tag/0095)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.ModuleSkyscraper

section Core
variable {X : TopCat.{u}} {R : X.Presheaf CommRingCat.{u}}

/-- The presheaf of rings underlying a presheaf of commutative rings, in the spelling
`PresheafOfModules` consumes. -/
abbrev ringCat (R : X.Presheaf CommRingCat.{u}) : X.Presheaf RingCat.{u} :=
  R ⋙ forget₂ CommRingCat.{u} RingCat.{u}

/-! ### The skyscraper presheaf of abelian groups -/

/-- The skyscraper presheaf of abelian groups at `x` with value `A`: its sections over `U` are
the functions from `PLift (x ∈ U)` to `A`, so they are `A` when `x ∈ U` and zero otherwise.
The restriction maps are precomposition with the implication between the two memberships. -/
noncomputable def skyAb (x : X) (A : Type u) [AddCommGroup A] :
    TopCat.Presheaf AddCommGrpCat.{u} X :=
  Stacks.Modules.skyscraperAbPresheaf x (AddCommGrpCat.of A)

/-- **The skyscraper is a sheaf.**  Over an open `U` a section is a function on a type with at
most one element, so a compatible family over a cover of `U` is glued by taking the value of
any member whose open contains `x`, and uniqueness is proof irrelevance. -/
theorem skyAb_isSheaf (x : X) (A : Type u) [AddCommGroup A] : (skyAb x A).IsSheaf :=
  Stacks.Modules.skyscraperAbPresheaf_isSheaf x (AddCommGrpCat.of A)

/-! ### The skyscraper presheaf of modules -/

/-- A section of `R` acts on the sections of the skyscraper through its germ at `x`. -/
noncomputable instance skyModule {x : X} (A : ModuleCat.{u} (R.stalk x)) (U : (Opens X)ᵒᵖ) :
    Module ↑((ringCat R).obj U) ↑((skyAb x ↑A).obj U) :=
  Stacks.Modules.skyscraperModuleSections R x A U

/-- A section `r` of `R` over `U` acts on a section of the skyscraper through the germ of `r`
at `x`. -/
@[simp] lemma skyModule_smul_apply {x : X} (A : ModuleCat.{u} (R.stalk x)) (U : (Opens X)ᵒᵖ)
    (r : ↑((ringCat R).obj U)) (g : ↑((skyAb x ↑A).obj U)) (p : PLift (x ∈ U.unop)) :
    (r • g) p = (R.germ U.unop x p.down).hom r • g p := rfl

/-- The skyscraper presheaf of `R`-modules at `x` with value `A`. -/
noncomputable def skyPresheaf {x : X} (A : ModuleCat.{u} (R.stalk x)) :
    PresheafOfModules.{u} (ringCat R) :=
  Stacks.Modules.skyscraperPresheaf R x A

/-- The underlying presheaf of abelian groups of `skyPresheaf A` is `skyAb x A`. -/
@[simp] lemma skyPresheaf_presheaf {x : X} (A : ModuleCat.{u} (R.stalk x)) :
    (skyPresheaf A).presheaf = skyAb x ↑A := rfl

/-! ### The stalk of a presheaf of modules -/

/-- The stalk at `x` of a presheaf of `R`-modules, as a module over the stalk of `R`. -/
noncomputable abbrev stalkObj (M : PresheafOfModules.{u} (ringCat R)) (x : X) :
    ModuleCat.{u} ↑(R.stalk x) :=
  ModuleCat.of _ ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x)

/-- Mathlib's `PresheafOfModules.germ_smul` in the spelling `.hom` produces. -/
lemma germ_smul' (M : PresheafOfModules.{u} (ringCat R)) (x : X) (U : Opens X) (hx : x ∈ U)
    (r : ↑(R.obj (op U))) (m : ↑(M.obj (op U))) :
    (TopCat.Presheaf.germ M.presheaf U x hx).hom (r • m)
      = (R.germ U x hx).hom r • (TopCat.Presheaf.germ M.presheaf U x hx).hom m :=
  PresheafOfModules.germ_smul M x U hx r m

variable {M N : PresheafOfModules.{u} (ringCat R)}

/-- The stalk map of a morphism of presheaves of modules, as a linear map over the stalk of
`R`. -/
noncomputable def stalkMapLinear (φ : M ⟶ N) (x : X) :
    ↑(TopCat.Presheaf.stalk M.presheaf x) →ₗ[↑(R.stalk x)]
      ↑(TopCat.Presheaf.stalk N.presheaf x) :=
  Stacks.Modules.stalkLinearMap φ

/-- `stalkMapLinear φ x` sends the germ of a section `m` to the germ of `φ m`. -/
@[simp] lemma stalkMapLinear_germ (φ : M ⟶ N) (x : X) (U : Opens X) (hx : x ∈ U)
    (m : ↑(M.obj (op U))) :
    stalkMapLinear φ x ((TopCat.Presheaf.germ M.presheaf U x hx).hom m)
      = (TopCat.Presheaf.germ N.presheaf U x hx).hom ((φ.app (op U)).hom m) :=
  Stacks.Modules.stalkLinearMap_germ φ U hx m

end Core

/-! ### The stalk and skyscraper functors -/

section Functors

variable {X : TopCat.{u}} (R : X.Presheaf CommRingCat.{u}) (x : X)

/-- The stalk functor at `x` on presheaves of `R`-modules. -/
noncomputable def presheafStalkFunctor :
    PresheafOfModules.{u} (ringCat R) ⥤ ModuleCat.{u} ↑(R.stalk x) :=
  Stacks.Modules.stalkPresheafFunctor R x

/-- The skyscraper functor at `x` into presheaves of `R`-modules. -/
noncomputable def skyPresheafFunctor :
    ModuleCat.{u} ↑(R.stalk x) ⥤ PresheafOfModules.{u} (ringCat R) :=
  Stacks.Modules.skyscraperPresheafFunctor R x

/-- The stalk functor sends `M` to its stalk `stalkObj M x`. -/
@[simp] lemma presheafStalkFunctor_obj (M : PresheafOfModules.{u} (ringCat R)) :
    (presheafStalkFunctor R x).obj M = stalkObj M x := rfl

/-- The skyscraper functor sends `A` to the skyscraper presheaf `skyPresheaf A`. -/
@[simp] lemma skyPresheafFunctor_obj (A : ModuleCat.{u} ↑(R.stalk x)) :
    (skyPresheafFunctor R x).obj A = skyPresheaf A := rfl

/-- The skyscraper functor applies a linear map `φ` pointwise to sections. -/
@[simp] lemma skyPresheafFunctor_map_app_apply {A B : ModuleCat.{u} ↑(R.stalk x)} (φ : A ⟶ B)
    (U : (Opens X)ᵒᵖ) (g : ↑((skyPresheaf A).obj U)) (p : PLift (x ∈ U.unop)) :
    (((skyPresheafFunctor R x).map φ).app U).hom g p = φ.hom (g p) := rfl

end Functors

/-! ### The stalk-skyscraper adjunction on presheaves of modules -/

section Adjunction

variable {X : TopCat.{u}} {R : X.Presheaf CommRingCat.{u}} {x : X}
  {M : PresheafOfModules.{u} (ringCat R)} {A : ModuleCat.{u} (R.stalk x)}

/-- The linear map out of the stalk determined by a morphism into the skyscraper. -/
noncomputable def fromStalkLinear (β : M ⟶ skyPresheaf A) : stalkObj M x ⟶ A :=
  ModuleCat.ofHom (Stacks.Modules.stalkMapOfSkyscraperPresheafHom R x A M β)

/-- `fromStalkLinear β` sends the germ of a section `m` over `U` to the value of `β m` at the
membership `x ∈ U`. -/
@[simp] lemma fromStalkLinear_germ (β : M ⟶ skyPresheaf A) (U : Opens X) (hx : x ∈ U)
    (m : ↑(M.obj (op U))) :
    (fromStalkLinear β).hom ((TopCat.Presheaf.germ M.presheaf U x hx).hom m)
      = (β.app (op U)).hom m ⟨hx⟩ :=
  Stacks.Modules.stalkMapOfSkyscraperPresheafHom_germ R x A M β U hx m

/-- The morphism of presheaves of modules into the skyscraper determined by a linear map out
of the stalk. -/
noncomputable def toSky (α : stalkObj M x ⟶ A) : M ⟶ skyPresheaf A :=
  Stacks.Modules.skyscraperPresheafHom R x A M α.hom

/-- Over `U`, `toSky α` sends a section `m` to the function whose value is `α` applied to the germ
of `m` at `x`. -/
@[simp] lemma toSky_app_apply (α : stalkObj M x ⟶ A) (U : (Opens X)ᵒᵖ) (m : ↑(M.obj U))
    (p : PLift (x ∈ U.unop)) :
    ((toSky α).app U).hom m p
      = α.hom ((TopCat.Presheaf.germ M.presheaf U.unop x p.down).hom m) := rfl

/-- **The stalk-skyscraper hom bijection.**  A linear map out of the stalk of `M` at `x` is
the same thing as a morphism of presheaves of modules from `M` into the skyscraper at `x`. -/
noncomputable def homEquivSky (M : PresheafOfModules.{u} (ringCat R))
    (A : ModuleCat.{u} (R.stalk x)) :
    (stalkObj M x ⟶ A) ≃ (M ⟶ skyPresheaf A) :=
  (ModuleCat.homEquiv (M := stalkObj M x) (N := A)).trans
    (Stacks.Modules.skyscraperPresheafHomEquiv R x A M).symm

/-- Precomposition on the skyscraper side of the bijection is the stalk map on the other. -/
lemma fromStalkLinear_comp {M' : PresheafOfModules.{u} (ringCat R)} (f : M' ⟶ M)
    (g : M ⟶ skyPresheaf A) :
    fromStalkLinear (f ≫ g)
      = ModuleCat.ofHom (stalkMapLinear f x) ≫ fromStalkLinear g := by
  ext m
  obtain ⟨U, hU, m₀, hm⟩ := TopCat.Presheaf.exists_germ_eq M'.presheaf m
  subst hm
  exact (fromStalkLinear_germ (f ≫ g) U hU m₀).trans
    (((congrArg (fromStalkLinear g).hom (stalkMapLinear_germ f x U hU m₀)).trans
      (fromStalkLinear_germ g U hU ((f.app (op U)).hom m₀))).symm)

end Adjunction

section AdjunctionDef

variable {X : TopCat.{u}} (R : X.Presheaf CommRingCat.{u}) (x : X)

/-- **The stalk functor on presheaves of modules is left adjoint to the skyscraper functor.**
This is the only input the stalk formula for a pullback needs: both sides of that formula are
left adjoints, and their right adjoints agree. -/
noncomputable def stalkSkyAdjunction :
    presheafStalkFunctor R x ⊣ skyPresheafFunctor R x :=
  Stacks.Modules.stalkSkyscraperPresheafAdjunction R x

end AdjunctionDef

/-! ### The skyscraper sheaf of modules on a scheme, and the adjunction there -/

section Scheme

open AlgebraicGeometry

variable (X : Scheme.{u}) (x : X)

/-- The skyscraper sheaf of `𝒪_X`-modules at `x` with value `A`.  The sheaf condition is
`skyAb_isSheaf`; the underlying presheaf of modules is `skyPresheaf A`, which typechecks
against `X.ringCatSheaf` because `X.ringCatSheaf.obj` is `X.presheaf ⋙ forget₂ CommRingCat
RingCat` by definition. -/
noncomputable def skyModules (A : ModuleCat.{u} (X.presheaf.stalk x)) : X.Modules :=
  ⟨skyPresheaf A, skyAb_isSheaf x ↑A⟩

/-- The skyscraper functor into `𝒪_X`-modules. -/
noncomputable def skyModulesFunctor :
    ModuleCat.{u} ↑(X.presheaf.stalk x) ⥤ X.Modules where
  obj A := skyModules X x A
  map φ := ⟨(skyPresheafFunctor X.presheaf x).map φ⟩
  map_id _A := rfl
  map_comp _φ _ψ := rfl

/-- The stalk functor on `𝒪_X`-modules, valued in modules over the local ring at `x`. -/
noncomputable def modulesStalkFunctor :
    X.Modules ⥤ ModuleCat.{u} ↑(X.presheaf.stalk x) :=
  SheafOfModules.forget X.ringCatSheaf ⋙ presheafStalkFunctor X.presheaf x

/-- **The stalk functor on `𝒪_X`-modules is left adjoint to the skyscraper functor.**  The
hom bijection is the one for presheaves of modules, transported along the full faithfulness
of the forgetful functor from sheaves to presheaves of modules. -/
noncomputable def modulesStalkSkyAdjunction :
    modulesStalkFunctor X x ⊣ skyModulesFunctor X x :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M A ↦ (homEquivSky M.val A).trans
        { toFun := fun β ↦ ⟨β⟩
          invFun := fun β ↦ β.val
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl }
      homEquiv_naturality_left_symm := fun f g ↦
        fromStalkLinear_comp (x := x) f.val g.val
      homEquiv_naturality_right := fun _f _g ↦ rfl }

/-- The stalk functor on `𝒪_X`-modules is a left adjoint. -/
instance isLeftAdjoint_modulesStalkFunctor : (modulesStalkFunctor X x).IsLeftAdjoint :=
  (modulesStalkSkyAdjunction X x).isLeftAdjoint

/-- The skyscraper functor into `𝒪_X`-modules is a right adjoint. -/
instance isRightAdjoint_skyModulesFunctor : (skyModulesFunctor X x).IsRightAdjoint :=
  (modulesStalkSkyAdjunction X x).isRightAdjoint

end Scheme

/-! ### The pushforward of a skyscraper, and the stalk of a pullback -/

section Pullback

open AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)

/-- Reindexing the sections of a skyscraper along `x ∈ f⁻¹V ↔ f x ∈ V`.  The two index types
are definitionally equal, so the map is `g ↦ fun p ↦ g ⟨p.down⟩`; writing it this way rather
than as the identity avoids depending on their being syntactically equal. -/
noncomputable def pushSkyAbHom (A : ModuleCat.{u} (X.presheaf.stalk x)) :
    ((Scheme.Modules.pushforward f).obj (skyModules X x A)).val.presheaf ⟶
      (skyModules Y (f x)
        ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj A)).val.presheaf where
  app V := AddCommGrpCat.ofHom
    { toFun := fun g p ↦ g ⟨p.down⟩
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }

/-- The comparison `f_*(sky_x A) ⟶ sky_{f x}(A)`.  Its content is that a section of `𝒪_Y` over
`V` acts on the left through `f^♯_V` followed by the germ at `x`, and on the right through the
germ at `f x` followed by the stalk map of `f`, and those agree. -/
noncomputable def pushSkyHom (A : ModuleCat.{u} (X.presheaf.stalk x)) :
    (Scheme.Modules.pushforward f).obj (skyModules X x A) ⟶
      skyModules Y (f x) ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj A) :=
  ⟨PresheafOfModules.homMk (pushSkyAbHom f x A) (fun V r g ↦ funext fun p ↦ by
    change (X.presheaf.germ ((Opens.map f.base).obj V.unop) x p.down).hom
        ((f.app V.unop).hom r) • g ⟨p.down⟩
      = (f.stalkMap x).hom ((Y.presheaf.germ V.unop (f x) p.down).hom r) • g ⟨p.down⟩
    rw [Scheme.Hom.germ_stalkMap_apply f V.unop x p.down r])⟩

/-- The reindexing of `pushSkyAbHom` in the other direction. -/
noncomputable def pushSkyAbInv (A : ModuleCat.{u} (X.presheaf.stalk x)) :
    (skyModules Y (f x)
        ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj A)).val.presheaf ⟶
      ((Scheme.Modules.pushforward f).obj (skyModules X x A)).val.presheaf where
  app V := AddCommGrpCat.ofHom
    { toFun := fun g p ↦ g ⟨p.down⟩
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }

/-- The inverse of `pushSkyHom`. -/
noncomputable def pushSkyInv (A : ModuleCat.{u} (X.presheaf.stalk x)) :
    skyModules Y (f x) ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj A) ⟶
      (Scheme.Modules.pushforward f).obj (skyModules X x A) :=
  ⟨PresheafOfModules.homMk (pushSkyAbInv f x A) (fun V r g ↦ funext fun p ↦ by
    change (f.stalkMap x).hom ((Y.presheaf.germ V.unop (f x) p.down).hom r) • g ⟨p.down⟩
      = (X.presheaf.germ ((Opens.map f.base).obj V.unop) x p.down).hom
          ((f.app V.unop).hom r) • g ⟨p.down⟩
    rw [Scheme.Hom.germ_stalkMap_apply f V.unop x p.down r])⟩

/-- **The pushforward of a skyscraper at `x` is the skyscraper at `f x`**, with the value read
as a module over `𝒪_{Y,f x}` along the stalk map of `f`. -/
noncomputable def pushSkyObjIso (A : ModuleCat.{u} (X.presheaf.stalk x)) :
    (Scheme.Modules.pushforward f).obj (skyModules X x A) ≅
      skyModules Y (f x) ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj A) where
  hom := pushSkyHom f x A
  inv := pushSkyInv f x A
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- `pushSkyObjIso`, naturally in the value: the two right adjoints of the stalk formula for a
pullback are isomorphic. -/
noncomputable def pushSkyIso :
    skyModulesFunctor X x ⋙ Scheme.Modules.pushforward f ≅
      ModuleCat.restrictScalars (f.stalkMap x).hom ⋙ skyModulesFunctor Y (f x) :=
  NatIso.ofComponents (pushSkyObjIso f x) (fun _ ↦ rfl)

/-- **Stacks 0098 for Mathlib's pullback of sheaves of modules on schemes.**  The stalk at `x`
of the pullback along `f` is the base change of the stalk at `f x` along the stalk map of `f`:

`(f^*N)_x = 𝒪_{X,x} ⊗_{𝒪_{Y,f x}} N_{f x}`,

naturally in `N`.  Both sides are left adjoints — `pullback f ⋙ stalk_x` by
`Scheme.Modules.pullbackPushforwardAdjunction` composed with `modulesStalkSkyAdjunction`, and
`stalk_{f x} ⋙ extendScalars` by `modulesStalkSkyAdjunction` composed with
`ModuleCat.extendRestrictScalarsAdj` — and `pushSkyIso` identifies their right adjoints, so
`CategoryTheory.conjugateIsoEquiv` identifies them.  No description of the sections of the
pullback, and no colimit interchange, is used.

**On the covering set.**  Tag 0098 is also carried by
`PullbackStalkTensor.stalkPullbackTensorIso` (`StacksFrontier/Topology/Sheaves/RingedSpace/ModulePullbackStalk.lean`), and the two
declarations state different things, which is what the covering-set rule requires of a shared
tag.  That one works over an arbitrary morphism of *ringed spaces* and computes the stalk of the
hand-built model `O_X ⊗_{f^{-1}O_Y} f^{-1}G` of Tag 0095 (2), at a single object, as a linear
equivalence; it does not know that model to be a pullback functor.  This one works over a
morphism of *schemes*, is about Mathlib's `Scheme.Modules.pullback` itself, and is natural in
`N`.  Neither subsumes the other: the first is more general in its spaces, the second in what it
identifies. -/
@[stacks 0098 "the stalk of Mathlib's `Scheme.Modules.pullback` at `x`, naturally in the module; \
the companion carrier `PullbackStalkTensor.stalkPullbackTensorIso` instead computes the stalk of \
the hand-built Tag 0095 (2) model over an arbitrary morphism of ringed spaces"]
noncomputable def pullbackStalkIso :
    modulesStalkFunctor Y (f x) ⋙ ModuleCat.extendScalars (f.stalkMap x).hom ≅
      Scheme.Modules.pullback f ⋙ modulesStalkFunctor X x :=
  (conjugateIsoEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp (modulesStalkSkyAdjunction X x))
    ((modulesStalkSkyAdjunction Y (f x)).comp
      (ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom))).symm (pushSkyIso f x)

/-- **Stacks 0098**, read on an object: for an `𝒪_Y`-module `N`, the stalk of `f^*N` at `x` is
`𝒪_{X,x} ⊗_{𝒪_{Y,f x}} N_{f x}` as a module over `𝒪_{X,x}`. -/
noncomputable def pullbackStalkObjIso (N : Y.Modules) :
    (ModuleCat.extendScalars (f.stalkMap x).hom).obj (stalkObj N.val (f x))
      ≅ stalkObj ((Scheme.Modules.pullback f).obj N).val x :=
  (pullbackStalkIso f x).app N

/-- `pullbackStalkObjIso` as an `𝒪_{X,x}`-linear equivalence, which is the form a consumer
reasoning about the stalk as a module — associated primes, flatness, finiteness — needs.  The
type is left to be inferred: the source is `𝒪_{X,x} ⊗_{𝒪_{Y,f x}} N_{f x}`, whose `Module`
structure over `𝒪_{Y,f x}` comes from the algebra structure `ModuleCat.extendScalars`
installs from the stalk map and is not available as a global instance. -/
noncomputable def pullbackStalkLinearEquiv (N : Y.Modules) :=
  (pullbackStalkObjIso f x N).toLinearEquiv

end Pullback

end Stacks.ModuleSkyscraper

