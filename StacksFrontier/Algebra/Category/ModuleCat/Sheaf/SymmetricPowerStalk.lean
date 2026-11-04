module

public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Topology.Sheaves.Sheafify
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerSheafification
public import StacksCore.Tactic.StacksAttribute

/-!
# Stalks of the symmetric algebra and of the symmetric powers of a presheaf of modules

Let `R` be a presheaf of commutative rings on a topological space `X` and `F` a presheaf of
`R`-modules. This file proves that forming the symmetric algebra, and forming the `n`-th
symmetric power, commute with taking the stalk at a point `x : X`:

* `PresheafOfModules.symAlgStalkRingEquiv` : the stalk of the presheaf of rings
  `U ↦ Sym_{R(U)}(F(U))` is `Sym_{R_x}(F_x)`;
* `PresheafOfModules.symPowStalkEquiv` : the stalk of the presheaf of modules
  `U ↦ Symⁿ_{R(U)}(F(U))` — that is, of `PresheafOfModules.symPow n F` — is `Symⁿ_{R_x}(F_x)`,
  as a module over the stalk ring `R_x`.

The second statement is the point-local half of Stacks Tags 01CG and 01CH. Tag 01CG identifies
the degree-`n` symmetric power of a *sheaf* of modules on a ringed space with the sheafification
of `U ↦ Symⁿ_{O(U)}(F(U))` — which for an arbitrary package of algebras is
`SheafOfModules.symmetricPowerSheafifyIso` in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AlgebraBundleStalk`, by `rfl` — and since
sheafification does not change stalks, the stalk of `Symⁿ F` is the stalk of that presheaf.
This file computes exactly that stalk.

## Main definitions

* `PresheafOfModules.germₛₗ` : the germ map of a presheaf of modules, as a semilinear map over
  the germ map of the presheaf of rings. The semilinearity is Mathlib's
  `PresheafOfModules.germ_smul`.
* `PresheafOfModules.symAlg` : the presheaf of commutative rings whose sections over `U` are
  `Sym_{R(U)}(F(U))`, with `SymmetricAlgebra.mapₛₗ` of the restriction maps as its restriction
  maps.
* `PresheafOfModules.symAlgGerm` : the germ map of `symAlg F`, as a ring homomorphism whose
  source is spelled as the symmetric algebra itself.
* `PresheafOfModules.symAlgStalkDesc` : base change along the germ maps,
  `(Sym F)_x ⟶ Sym_{R_x}(F_x)`, obtained from the colimit computing the stalk.
* `PresheafOfModules.stalkAlgebra` and `PresheafOfModules.ιStalkL` : the `R_x`-algebra structure
  on `(Sym F)_x` induced by the structure map `R ⟶ symAlg F`, and the `R_x`-linear degree-one
  generator `F_x →ₗ (Sym F)_x`. These are the data the universal property of the symmetric
  algebra consumes.
* `PresheafOfModules.symAlgStalkLift` : the `R_x`-algebra map `Sym_{R_x}(F_x) ⟶ (Sym F)_x`
  lifting `ιStalkL`.
* `PresheafOfModules.symPowStalkDesc` and `PresheafOfModules.symPowStalkL` : the same base
  change in degree `n`, as a morphism of abelian groups and as an `R_x`-linear map.

## Main results

* `PresheafOfModules.symAlgStalkRingEquiv` : **the symmetric algebra commutes with stalks.**
  `symAlgStalkDesc` and `symAlgStalkLift` are mutually inverse: that is
  `symAlgStalkLift_symAlgStalkDesc` and `symAlgStalkDesc_symAlgStalkLift`, each proved by
  `SymmetricAlgebra.ringHom_ext` after reducing to a germ with
  `TopCat.Presheaf.exists_germ_eq`.
* `PresheafOfModules.symPowStalkEquiv` : **the `n`-th symmetric power commutes with stalks.**
  Injectivity (`symPowStalkL_injective`) is deduced from injectivity of `symAlgStalkDesc`
  together with `TopCat.Presheaf.germ_eq`; surjectivity (`symPowStalkL_surjective`) from
  `SymmetricAlgebra.symmetricPower_eq_span_prod_ι`, after choosing one open neighbourhood on
  which representatives of all `n` germs are defined simultaneously.
* `PresheafOfModules.symPowStalkL_germ_prod_ι` : the comparison sends the germ of a product of
  `n` degree-one generators to the product of the germs. This is the formula Tag 01CH's
  comparison is specified by.

## Implementation notes

**Why the whole symmetric algebra and not only the degree-`n` piece.** Surjectivity of the
degree-`n` comparison is elementary — a finite family of germs has a common open neighbourhood —
but injectivity is not: a local section of `Symⁿ` whose germ-wise base change vanishes must
already vanish on a smaller open, and that is precisely the statement that `Sym` commutes with
the filtered colimit computing the stalk. The ungraded symmetric algebra is where the universal
property is available, so it is proved there (`symAlgStalkRingEquiv`) and transported down to
degree `n` through the inclusion `Symⁿ_{R(U)}(F(U)) ⊆ Sym_{R(U)}(F(U))`, which is injective on
stalks because it is injective sectionwise.

**The degree is always a variable.** Every statement about `symPow`, `symMapₛₗ` or
`SymmetricAlgebra.prod_ι_mem` below keeps `n` a variable and is instantiated only at the point
of use. `SymmetricAlgebra R M` is a reducible abbreviation for a `RingCon` quotient of
`TensorAlgebra R M`, and with a numeral degree `whnf` unfolds `symmetricPower (1 + 1)` through
`Submodule.mul` and `Submodule.span` into that quotient; this is fatal in a *statement*, not
only in a proof.

**Two spellings of the same type, and the three places it matters.** The sections of `symAlg F`
over `U` are `↑((symAlg F).obj (op U))`, and `SymmetricAlgebra ((R ⋙ forget₂ _ _).obj (op U))
(F.obj (op U))` is the same type definitionally but not syntactically; `rw` works at a
transparency at which the first spelling's multiplication is not the second's, so `map_mul` does
not fire through it. `symAlgGerm` exists to ascribe the second spelling, and `ιStalkFun` and
`symPowStalkFun` do the same for the targets of the two `colimit.desc` morphisms, whose codomains
are `AddCommGrpCat.of` of the type one actually wants. All three are definitional renames.

**Universes.** `X : TopCat.{u}`, `R : X.Presheaf CommRingCat.{u}` and
`F : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)` is the single combination at which
Mathlib's `Module (R.stalk x) ↑(TopCat.Presheaf.stalk F.presheaf x)` instance
(`Mathlib/Algebra/Category/ModuleCat/Stalk.lean`) exists, so the module universe is forced equal
to the ring universe and to the universe of the space. Nothing is narrowed relative to that
instance; this is the same constraint recorded in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness`.

**No `@[stacks]` tag.** Tags 01CG and 01CH are statements about a sheaf of modules on a ringed
space: 01CG that `Symⁿ F` is the sheafification of the sectionwise symmetric powers, 01CH that
its stalk is `Symⁿ` of the stalk. The first is `SheafOfModules.symmetricPowerSheafifyIso`; the
second needs this file's `symPowStalkEquiv` *composed with* the fact that the sheafification unit
is a stalk isomorphism, which is not proved here. Tagging a declaration below would report
either tag as covered when only this half is.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 01CH](https://stacks.math.columbia.edu/tag/01CH)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace PresheafOfModules

variable {X : TopCat.{u}} {R : X.Presheaf CommRingCat.{u}}
  (F : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})) (x : X)

/-- The germ at `x` of a presheaf of modules, as a semilinear map over the germ ring map. -/
noncomputable def germₛₗ (U : Opens X) (hx : x ∈ U) :
    F.obj (op U) →ₛₗ[(R.germ U x hx).hom] ↑(TopCat.Presheaf.stalk F.presheaf x) where
  toFun s := TopCat.Presheaf.germ F.presheaf U x hx s
  map_add' s t := map_add _ s t
  map_smul' r s := F.germ_smul x U hx r s

/-- `germₛₗ F x U hx` sends a section to its germ at `x`. -/
@[simp]
theorem germₛₗ_apply (U : Opens X) (hx : x ∈ U) (s : F.obj (op U)) :
    germₛₗ F x U hx s = TopCat.Presheaf.germ F.presheaf U x hx s := rfl

/-- The presheaf of commutative rings whose sections over `U` are `Sym_{O(U)}(F(U))`. -/
noncomputable def symAlg : X.Presheaf CommRingCat.{u} where
  obj U := CommRingCat.of
    (SymmetricAlgebra ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj U) (F.obj U))
  map {U _} f := CommRingCat.ofHom
    (SymmetricAlgebra.mapₛₗ ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).map f).hom
      (F.restrictₛₗ f))
  map_id U := by
    refine CommRingCat.hom_ext (RingHom.ext fun y => ?_)
    exact SymmetricAlgebra.mapₛₗ_eq_self (F.restrictₛₗ (𝟙 U))
      (fun r => congrArg (fun φ : (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj U ⟶
          (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj U => (ConcreteCategory.hom φ) r)
        ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).map_id U))
      (fun m => F.map_id_apply_ungraded U m) y
  map_comp {U _ W} f g := by
    refine CommRingCat.hom_ext (RingHom.ext fun y => ?_)
    exact SymmetricAlgebra.mapₛₗ_eq_comp (F.restrictₛₗ f) (F.restrictₛₗ g) (F.restrictₛₗ (f ≫ g))
      (fun r => congrArg (fun φ : (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj U ⟶
          (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj W => (ConcreteCategory.hom φ) r)
        ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).map_comp f g))
      (fun m => F.map_comp_apply f g m) y

/-- The restriction maps of `symAlg F` are `SymmetricAlgebra.mapₛₗ` of the restriction maps of
`R` and of `F`. -/
@[simp]
theorem symAlg_map_apply {U V : (Opens X)ᵒᵖ} (f : U ⟶ V)
    (y : SymmetricAlgebra ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj U) (F.obj U)) :
    (symAlg F).map f y =
      SymmetricAlgebra.mapₛₗ ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).map f).hom
        (F.restrictₛₗ f) y := rfl

/-- The germ map of `symAlg F` as a ring homomorphism out of the sectionwise symmetric algebra.
This is `TopCat.Presheaf.germ` with its source spelled as the symmetric algebra itself rather
than as the value of a functor; the two are definitionally equal, but the first spelling is the
one in which the ring structure used by `map_mul` is found by instance search. -/
noncomputable def symAlgGerm (U : Opens X) (hx : x ∈ U) :
    SymmetricAlgebra ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) (F.obj (op U)) →+*
      ↑((symAlg F).stalk x) :=
  ((symAlg F).germ U x hx).hom

/-- `symAlgGerm F x U hx` sends a section of `symAlg F` over `U` to its germ at `x`. -/
theorem symAlgGerm_eq (U : Opens X) (hx : x ∈ U)
    (y : SymmetricAlgebra ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
      (F.obj (op U))) :
    symAlgGerm F x U hx y = (symAlg F).germ U x hx y := rfl

/-- The cocone on the diagram computing the stalk of `symAlg F` whose component at an open
neighbourhood `U` of `x` is base change along the germ maps of `R` and of `F`. -/
noncomputable def symAlgStalkCocone :
    Limits.Cocone ((OpenNhds.inclusion x).op ⋙ symAlg F) where
  pt := CommRingCat.of
    (SymmetricAlgebra ↑(R.stalk x) ↑(TopCat.Presheaf.stalk F.presheaf x))
  ι :=
    { app := fun U => CommRingCat.ofHom
        (SymmetricAlgebra.mapₛₗ (R.germ U.unop.1 x U.unop.2).hom
          (germₛₗ F x U.unop.1 U.unop.2))
      naturality := fun U V f => by
        refine CommRingCat.hom_ext (RingHom.ext fun y => ?_)
        exact (SymmetricAlgebra.mapₛₗ_eq_comp
          (F.restrictₛₗ ((OpenNhds.inclusion x).op.map f))
          (germₛₗ F x V.unop.1 V.unop.2) (germₛₗ F x U.unop.1 U.unop.2)
          (fun r => (TopCat.Presheaf.germ_res_apply' R
            ((OpenNhds.inclusion x).op.map f) x V.unop.2 r).symm)
          (fun m => (TopCat.Presheaf.germ_res_apply' F.presheaf
            ((OpenNhds.inclusion x).op.map f) x V.unop.2 m).symm) y).symm }

/-- Base change of the symmetric algebra along the germ maps, out of the stalk of the presheaf
of sectionwise symmetric algebras. -/
noncomputable def symAlgStalkDesc :
    (symAlg F).stalk x ⟶
      CommRingCat.of (SymmetricAlgebra ↑(R.stalk x) ↑(TopCat.Presheaf.stalk F.presheaf x)) :=
  Limits.colimit.desc _ (symAlgStalkCocone F x)

/-- `symAlgStalkDesc` sends the germ of a section `y` of `symAlg F` over `U` to the base change
of `y` along the germ maps of `R` and of `F`. -/
@[simp]
theorem symAlgStalkDesc_germ (U : Opens X) (hx : x ∈ U)
    (y : SymmetricAlgebra ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
      (F.obj (op U))) :
    symAlgStalkDesc F x (symAlgGerm F x U hx y) =
      SymmetricAlgebra.mapₛₗ (R.germ U x hx).hom (germₛₗ F x U hx) y := by
  exact Limits.colimit.ι_desc_apply (symAlgStalkCocone F x) (op ⟨U, hx⟩) y

/-! ### The structure map and the degree-one generator on stalks -/

/-- The structure map `O ⟶ Sym(F)` of the presheaf of sectionwise symmetric algebras. -/
noncomputable def symAlgUnit : R ⟶ symAlg F where
  app U := CommRingCat.ofHom
    (algebraMap ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj U)
      (SymmetricAlgebra ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj U) (F.obj U)))
  naturality _ _ f := by
    refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
    exact (SymmetricAlgebra.mapₛₗ_algebraMap
      ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).map f).hom (F.restrictₛₗ f) r).symm

/-- The stalk of the presheaf of sectionwise symmetric algebras, as an algebra over the stalk
of the presheaf of rings. -/
noncomputable instance stalkAlgebra : Algebra ↑(R.stalk x) ↑((symAlg F).stalk x) :=
  ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map (symAlgUnit F)).hom.toAlgebra

/-- The structure map of the `R_x`-algebra `(symAlg F).stalk x` is the map induced on stalks by
`symAlgUnit F`. -/
theorem algebraMap_stalkAlgebra :
    algebraMap ↑(R.stalk x) ↑((symAlg F).stalk x) =
      ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map (symAlgUnit F)).hom := rfl

/-- The structure map of `(symAlg F).stalk x` sends the germ of `r : R(U)` to the germ of the
image of `r` in `Sym_{R(U)}(F(U))`. -/
@[simp]
theorem algebraMap_stalkAlgebra_germ (U : Opens X) (hx : x ∈ U) (r : ↑(R.obj (op U))) :
    algebraMap ↑(R.stalk x) ↑((symAlg F).stalk x) (R.germ U x hx r) =
      symAlgGerm F x U hx (algebraMap ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
        (SymmetricAlgebra ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
          (F.obj (op U))) r) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx (symAlgUnit F) r

/-- The cocone whose component at an open neighbourhood `U` of `x` sends a section of `F` to the
germ of its degree-one image in `Sym_{O(U)}(F(U))`. -/
noncomputable def ιStalkCocone :
    Limits.Cocone ((OpenNhds.inclusion x).op ⋙ F.presheaf) where
  pt := AddCommGrpCat.of ↑((symAlg F).stalk x)
  ι :=
    { app := fun U => AddCommGrpCat.ofHom
        (((symAlg F).germ U.unop.1 x U.unop.2).hom.toAddMonoidHom.comp
          (SymmetricAlgebra.ι
            ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U.unop.1))
            (F.obj (op U.unop.1))).toAddMonoidHom)
      naturality := fun U V f => by
        refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun m => ?_)
        exact Eq.trans
          (congrArg (fun z : SymmetricAlgebra
              ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op V.unop.1))
              (F.obj (op V.unop.1)) => (symAlg F).germ V.unop.1 x V.unop.2 z)
            (SymmetricAlgebra.mapₛₗ_ι
              ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).map
                ((OpenNhds.inclusion x).op.map f)).hom
              (F.restrictₛₗ ((OpenNhds.inclusion x).op.map f)) m).symm)
          (TopCat.Presheaf.germ_res_apply' (symAlg F)
            ((OpenNhds.inclusion x).op.map f) x V.unop.2
            (SymmetricAlgebra.ι ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U.unop.1))
              (F.obj (op U.unop.1)) m)) }

/-- The additive map from the stalk of `F` to the stalk of the presheaf of sectionwise symmetric
algebras, sending the germ of a section to the germ of its degree-one image. -/
noncomputable def ιStalkAdd :
    TopCat.Presheaf.stalk F.presheaf x ⟶ AddCommGrpCat.of ↑((symAlg F).stalk x) :=
  Limits.colimit.desc _ (ιStalkCocone F x)

/-- `ιStalkAdd` sends the germ of a section `m` of `F` to the germ of `SymmetricAlgebra.ι m`. -/
@[simp]
theorem ιStalkAdd_germ (U : Opens X) (hx : x ∈ U) (m : F.obj (op U)) :
    ιStalkAdd F x (TopCat.Presheaf.germ F.presheaf U x hx m) =
      symAlgGerm F x U hx (SymmetricAlgebra.ι
        ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) (F.obj (op U)) m) := by
  exact Limits.colimit.ι_desc_apply (ιStalkCocone F x) (op ⟨U, hx⟩) m

/-- The underlying function of `ιStalkAdd`, with its codomain spelled as the stalk ring. -/
noncomputable def ιStalkFun (m : ↑(TopCat.Presheaf.stalk F.presheaf x)) :
    ↑((symAlg F).stalk x) :=
  ιStalkAdd F x m

/-- `ιStalkFun` sends the germ of a section `m` of `F` to the germ of `SymmetricAlgebra.ι m`. -/
@[simp]
theorem ιStalkFun_germ (U : Opens X) (hx : x ∈ U) (m : F.obj (op U)) :
    ιStalkFun F x (TopCat.Presheaf.germ F.presheaf U x hx m) =
      symAlgGerm F x U hx (SymmetricAlgebra.ι
        ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) (F.obj (op U)) m) :=
  ιStalkAdd_germ F x U hx m

/-- `ιStalkFun` commutes with scalar multiplication by a germ of `R` on a germ of `F` defined
over the same open set. -/
theorem ιStalkFun_germ_smul (U : Opens X) (hx : x ∈ U)
    (a : (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) (b : F.obj (op U)) :
    ιStalkFun F x (R.germ U x hx a • TopCat.Presheaf.germ F.presheaf U x hx b) =
      R.germ U x hx a • ιStalkFun F x (TopCat.Presheaf.germ F.presheaf U x hx b) := by
  have h₁ : ιStalkFun F x (R.germ U x hx a • TopCat.Presheaf.germ F.presheaf U x hx b) =
      symAlgGerm F x U hx (SymmetricAlgebra.ι
        ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) (F.obj (op U)) (a • b)) := by
    rw [← F.germ_smul x U hx a b]
    exact ιStalkFun_germ F x U hx (a • b)
  have h₂ : SymmetricAlgebra.ι ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
        (F.obj (op U)) (a • b) =
      algebraMap ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
          (SymmetricAlgebra ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
            (F.obj (op U))) a *
        SymmetricAlgebra.ι ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
          (F.obj (op U)) b := by
    rw [map_smul, Algebra.smul_def]
  rw [h₁, h₂, map_mul (symAlgGerm F x U hx), ιStalkFun_germ, Algebra.smul_def,
    algebraMap_stalkAlgebra_germ]

/-- A scalar of the stalk ring and an element of a stalk of a presheaf of modules are germs of
sections over a common open neighbourhood of `x`. -/
private theorem exists_germ_eq_germ_smul_germ
    (G : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})) (r : ↑(R.stalk x))
    (m : ↑(TopCat.Presheaf.stalk G.presheaf x)) :
    ∃ (U : Opens X) (hx : x ∈ U) (a : (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
      (b : G.obj (op U)), R.germ U x hx a = r ∧ TopCat.Presheaf.germ G.presheaf U x hx b = m := by
  obtain ⟨U₁, h₁, r₀, hr⟩ := R.exists_germ_eq r
  obtain ⟨U₂, hle, h₂, m₀, hm⟩ := TopCat.Presheaf.exists_le_germ_eq G.presheaf m h₁
  exact ⟨U₂, h₂, R.map (homOfLE hle).op r₀, m₀,
    (TopCat.Presheaf.germ_res_apply R (homOfLE hle) x h₂ r₀).trans hr, hm⟩

/-- `ιStalkFun` is `R_x`-linear: it commutes with scalar multiplication by the stalk ring. -/
theorem ιStalkFun_smul (r : ↑(R.stalk x)) (m : ↑(TopCat.Presheaf.stalk F.presheaf x)) :
    ιStalkFun F x (r • m) = r • ιStalkFun F x m := by
  obtain ⟨U, hx, a, b, rfl, rfl⟩ := exists_germ_eq_germ_smul_germ x F r m
  exact ιStalkFun_germ_smul F x U hx a b

/-- The degree-one generator on stalks: the linear map from the stalk of `F` to the stalk of the
presheaf of sectionwise symmetric algebras. -/
noncomputable def ιStalkL :
    ↑(TopCat.Presheaf.stalk F.presheaf x) →ₗ[↑(R.stalk x)] ↑((symAlg F).stalk x) where
  toFun := ιStalkFun F x
  map_add' m m' := map_add _ m m'
  map_smul' r m := ιStalkFun_smul F x r m

/-- `ιStalkL` sends the germ of a section `m` of `F` to the germ of `SymmetricAlgebra.ι m`. -/
@[simp]
theorem ιStalkL_germ (U : Opens X) (hx : x ∈ U) (m : F.obj (op U)) :
    ιStalkL F x (TopCat.Presheaf.germ F.presheaf U x hx m) =
      symAlgGerm F x U hx (SymmetricAlgebra.ι
        ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) (F.obj (op U)) m) :=
  ιStalkFun_germ F x U hx m

/-- The algebra map from the symmetric algebra of the stalk to the stalk of the presheaf of
sectionwise symmetric algebras, induced by the degree-one generator on stalks. -/
noncomputable def symAlgStalkLift :
    SymmetricAlgebra ↑(R.stalk x) ↑(TopCat.Presheaf.stalk F.presheaf x) →ₐ[↑(R.stalk x)]
      ↑((symAlg F).stalk x) :=
  SymmetricAlgebra.lift (ιStalkL F x)

/-- `symAlgStalkLift` restricts to `ιStalkL` on degree-one generators. -/
@[simp]
theorem symAlgStalkLift_ι (m : ↑(TopCat.Presheaf.stalk F.presheaf x)) :
    symAlgStalkLift F x (SymmetricAlgebra.ι _ _ m) = ιStalkL F x m :=
  SymmetricAlgebra.lift_ι_apply (ιStalkL F x) m

/-! ### The two base-change maps are mutually inverse -/

/-- `symAlgStalkDesc` sends the germ of the image of `r : R(U)` in `Sym_{R(U)}(F(U))` to the image
of the germ of `r` in `Sym_{R_x}(F_x)`. -/
@[simp]
theorem symAlgStalkDesc_symAlgGerm_algebraMap (U : Opens X) (hU : x ∈ U)
    (r : (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) :
    symAlgStalkDesc F x (symAlgGerm F x U hU
        (algebraMap ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
          (SymmetricAlgebra ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
            (F.obj (op U))) r)) =
      algebraMap ↑(R.stalk x)
        (SymmetricAlgebra ↑(R.stalk x) ↑(TopCat.Presheaf.stalk F.presheaf x))
        (R.germ U x hU r) := by
  rw [symAlgStalkDesc_germ]
  exact SymmetricAlgebra.mapₛₗ_algebraMap _ _ r

/-- `symAlgStalkDesc` sends the germ of `SymmetricAlgebra.ι m` to `SymmetricAlgebra.ι` of the
germ of `m`. -/
@[simp]
theorem symAlgStalkDesc_symAlgGerm_ι (U : Opens X) (hU : x ∈ U) (m : F.obj (op U)) :
    symAlgStalkDesc F x (symAlgGerm F x U hU
        (SymmetricAlgebra.ι ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
          (F.obj (op U)) m)) =
      SymmetricAlgebra.ι ↑(R.stalk x) ↑(TopCat.Presheaf.stalk F.presheaf x)
        (TopCat.Presheaf.germ F.presheaf U x hU m) := by
  rw [symAlgStalkDesc_germ]
  exact SymmetricAlgebra.mapₛₗ_ι _ _ m

/-- `symAlgStalkLift` is a left inverse of `symAlgStalkDesc` on germs of sections of
`symAlg F`. -/
theorem symAlgStalkLift_symAlgStalkDesc_germ (U : Opens X) (hU : x ∈ U)
    (y : SymmetricAlgebra ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
      (F.obj (op U))) :
    symAlgStalkLift F x (symAlgStalkDesc F x (symAlgGerm F x U hU y)) =
      symAlgGerm F x U hU y := by
  have key : (symAlgStalkLift F x).toRingHom.comp
      (((symAlgStalkDesc F x).hom).comp (symAlgGerm F x U hU)) = symAlgGerm F x U hU := by
    refine SymmetricAlgebra.ringHom_ext (fun r => ?_) (fun m => ?_)
    · exact ((congrArg (fun z => symAlgStalkLift F x z)
          (symAlgStalkDesc_symAlgGerm_algebraMap F x U hU r)).trans
        ((symAlgStalkLift F x).commutes (R.germ U x hU r))).trans
        (algebraMap_stalkAlgebra_germ F x U hU r)
    · exact ((congrArg (fun z => symAlgStalkLift F x z)
          (symAlgStalkDesc_symAlgGerm_ι F x U hU m)).trans
        (symAlgStalkLift_ι F x (TopCat.Presheaf.germ F.presheaf U x hU m))).trans
        (ιStalkL_germ F x U hU m)
  exact DFunLike.congr_fun key y

/-- `symAlgStalkLift` is a left inverse of `symAlgStalkDesc`. -/
theorem symAlgStalkLift_symAlgStalkDesc (z : ↑((symAlg F).stalk x)) :
    symAlgStalkLift F x (symAlgStalkDesc F x z) = z := by
  obtain ⟨U, hU, y, rfl⟩ := (symAlg F).exists_germ_eq z
  exact symAlgStalkLift_symAlgStalkDesc_germ F x U hU y

/-- `symAlgStalkLift` is a right inverse of `symAlgStalkDesc`. -/
theorem symAlgStalkDesc_symAlgStalkLift
    (z : SymmetricAlgebra ↑(R.stalk x) ↑(TopCat.Presheaf.stalk F.presheaf x)) :
    symAlgStalkDesc F x (symAlgStalkLift F x z) = z := by
  have key : ((symAlgStalkDesc F x).hom).comp (symAlgStalkLift F x).toRingHom =
      RingHom.id (SymmetricAlgebra ↑(R.stalk x) ↑(TopCat.Presheaf.stalk F.presheaf x)) := by
    refine SymmetricAlgebra.ringHom_ext (fun s => ?_) (fun m => ?_)
    · obtain ⟨U, hU, r, rfl⟩ := R.exists_germ_eq s
      exact ((congrArg (fun z => symAlgStalkDesc F x z)
            (((symAlgStalkLift F x).commutes (R.germ U x hU r)).trans
              (algebraMap_stalkAlgebra_germ F x U hU r))).trans
          (symAlgStalkDesc_symAlgGerm_algebraMap F x U hU r))
    · obtain ⟨U, hU, b, rfl⟩ := TopCat.Presheaf.exists_germ_eq F.presheaf m
      exact ((congrArg (fun z => symAlgStalkDesc F x z)
            ((symAlgStalkLift_ι F x (TopCat.Presheaf.germ F.presheaf U x hU b)).trans
              (ιStalkL_germ F x U hU b))).trans
          (symAlgStalkDesc_symAlgGerm_ι F x U hU b))
  exact DFunLike.congr_fun key z

/-- **The symmetric algebra commutes with stalks.** The stalk at `x` of the presheaf of
sectionwise symmetric algebras of `F` is the symmetric algebra of the stalk of `F` over the
stalk of the presheaf of rings. -/
noncomputable def symAlgStalkRingEquiv :
    ↑((symAlg F).stalk x) ≃+*
      SymmetricAlgebra ↑(R.stalk x) ↑(TopCat.Presheaf.stalk F.presheaf x) :=
  RingEquiv.ofBijective (symAlgStalkDesc F x).hom
    ⟨Function.LeftInverse.injective (symAlgStalkLift_symAlgStalkDesc F x),
      Function.RightInverse.surjective (symAlgStalkDesc_symAlgStalkLift F x)⟩

/-- The base-change map `symAlgStalkDesc F x : (symAlg F).stalk x ⟶ Sym_{R_x}(F_x)` is
injective. -/
theorem symAlgStalkDesc_injective : Function.Injective (symAlgStalkDesc F x) :=
  Function.LeftInverse.injective (symAlgStalkLift_symAlgStalkDesc F x)

/-! ### The stalk of the presheaf of sectionwise symmetric powers -/

/-- The cocone on the diagram computing the stalk of `symPow n F` whose component at an open
neighbourhood `U` of `x` is base change of the `n`-th symmetric power along the germ maps. -/
noncomputable def symPowStalkCocone (n : ℕ) :
    Limits.Cocone ((OpenNhds.inclusion x).op ⋙ (symPow n F).presheaf) where
  pt := AddCommGrpCat.of
    (SymPow.symmetricPower n ↑(R.stalk x) ↑(TopCat.Presheaf.stalk F.presheaf x))
  ι :=
    { app := fun U => AddCommGrpCat.ofHom
        (SymPow.symMapₛₗ n (R.germ U.unop.1 x U.unop.2).hom
          (germₛₗ F x U.unop.1 U.unop.2)).toAddMonoidHom
      naturality := fun U V f => by
        refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun y => Subtype.ext ?_)
        exact (SymmetricAlgebra.mapₛₗ_eq_comp
          (F.restrictₛₗ ((OpenNhds.inclusion x).op.map f))
          (germₛₗ F x V.unop.1 V.unop.2) (germₛₗ F x U.unop.1 U.unop.2)
          (fun r => (TopCat.Presheaf.germ_res_apply' R
            ((OpenNhds.inclusion x).op.map f) x V.unop.2 r).symm)
          (fun m => (TopCat.Presheaf.germ_res_apply' F.presheaf
            ((OpenNhds.inclusion x).op.map f) x V.unop.2 m).symm) _).symm }

/-- Base change of the `n`-th symmetric power along the germ maps, out of the stalk of the
presheaf of sectionwise symmetric powers. -/
noncomputable def symPowStalkDesc (n : ℕ) :
    TopCat.Presheaf.stalk (symPow n F).presheaf x ⟶ AddCommGrpCat.of
      (SymPow.symmetricPower n ↑(R.stalk x) ↑(TopCat.Presheaf.stalk F.presheaf x)) :=
  Limits.colimit.desc _ (symPowStalkCocone F x n)

/-- The underlying function of `symPowStalkDesc`, with its codomain spelled as the symmetric
power of the stalk. -/
noncomputable def symPowStalkFun (n : ℕ)
    (t : ↑(TopCat.Presheaf.stalk (symPow n F).presheaf x)) :
    SymPow.symmetricPower n ↑(R.stalk x) ↑(TopCat.Presheaf.stalk F.presheaf x) :=
  symPowStalkDesc F x n t

/-- `symPowStalkFun` sends the germ of a section `y` of `symPow n F` over `U` to the base change
of `y` along the germ maps. -/
@[simp]
theorem symPowStalkFun_germ (n : ℕ) (U : Opens X) (hx : x ∈ U) (y : (symPow n F).obj (op U)) :
    symPowStalkFun F x n (TopCat.Presheaf.germ (symPow n F).presheaf U x hx y) =
      SymPow.symMapₛₗ n (R.germ U x hx).hom (germₛₗ F x U hx) y := by
  exact Limits.colimit.ι_desc_apply (symPowStalkCocone F x n) (op ⟨U, hx⟩) y

/-- `symPowStalkFun` commutes with scalar multiplication by a germ of `R` on a germ of
`symPow n F` defined over the same open set. -/
theorem symPowStalkFun_germ_smul (n : ℕ) (U : Opens X) (hx : x ∈ U)
    (a : (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) (y : (symPow n F).obj (op U)) :
    symPowStalkFun F x n (R.germ U x hx a •
        TopCat.Presheaf.germ (symPow n F).presheaf U x hx y) =
      R.germ U x hx a •
        symPowStalkFun F x n (TopCat.Presheaf.germ (symPow n F).presheaf U x hx y) := by
  rw [← (symPow n F).germ_smul x U hx a y, symPowStalkFun_germ, symPowStalkFun_germ]
  exact map_smulₛₗ (SymPow.symMapₛₗ n (R.germ U x hx).hom (germₛₗ F x U hx)) a y

/-- `symPowStalkFun` is `R_x`-linear: it commutes with scalar multiplication by the stalk
ring. -/
theorem symPowStalkFun_smul (n : ℕ) (r : ↑(R.stalk x))
    (t : ↑(TopCat.Presheaf.stalk (symPow n F).presheaf x)) :
    symPowStalkFun F x n (r • t) = r • symPowStalkFun F x n t := by
  obtain ⟨U, hx, a, y, rfl, rfl⟩ := exists_germ_eq_germ_smul_germ x (symPow n F) r t
  exact symPowStalkFun_germ_smul F x n U hx a y

/-- **The comparison map of Stacks 01CG and 01CH at a point**: base change of the `n`-th
symmetric power along the germ maps, as a linear map from the stalk of the presheaf of
sectionwise symmetric powers of `F` to the `n`-th symmetric power of the stalk of `F`. -/
noncomputable def symPowStalkL (n : ℕ) :
    ↑(TopCat.Presheaf.stalk (symPow n F).presheaf x) →ₗ[↑(R.stalk x)]
      SymPow.symmetricPower n ↑(R.stalk x) ↑(TopCat.Presheaf.stalk F.presheaf x) where
  toFun := symPowStalkFun F x n
  map_add' t t' := map_add _ t t'
  map_smul' r t := symPowStalkFun_smul F x n r t

/-- `symPowStalkL` sends the germ of a section `y` of `symPow n F` over `U` to the base change of
`y` along the germ maps. -/
@[simp]
theorem symPowStalkL_germ (n : ℕ) (U : Opens X) (hx : x ∈ U) (y : (symPow n F).obj (op U)) :
    symPowStalkL F x n (TopCat.Presheaf.germ (symPow n F).presheaf U x hx y) =
      SymPow.symMapₛₗ n (R.germ U x hx).hom (germₛₗ F x U hx) y :=
  symPowStalkFun_germ F x n U hx y

/-! ### The comparison map is bijective -/

/-- If base change of a local section of `Symⁿ F` along the germ maps vanishes, then its germ
vanishes. This is the injectivity half of Stacks 01CG/01CH at a point: it is where the symmetric
algebra has to be known to commute with the filtered colimit computing the stalk, and it is
deduced from `symAlgStalkDesc_injective`. -/
theorem germ_eq_zero_of_symMapₛₗ_eq_zero (n : ℕ) (U : Opens X) (hU : x ∈ U)
    (y : SymPow.symmetricPower n ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
      (F.obj (op U)))
    (h : SymmetricAlgebra.mapₛₗ (R.germ U x hU).hom (germₛₗ F x U hU)
      (y : SymmetricAlgebra ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
        (F.obj (op U))) = 0) :
    TopCat.Presheaf.germ (symPow n F).presheaf U x hU y = 0 := by
  have h0 : symAlgGerm F x U hU
      (y : SymmetricAlgebra ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
        (F.obj (op U))) = symAlgGerm F x U hU 0 := by
    refine symAlgStalkDesc_injective F x ?_
    rw [symAlgStalkDesc_germ, symAlgStalkDesc_germ, h, map_zero]
  obtain ⟨W, hW, iU, iV, heq⟩ := TopCat.Presheaf.germ_eq (symAlg F) x hU hU
    (y : SymmetricAlgebra ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
      (F.obj (op U))) 0
    ((symAlgGerm_eq F x U hU _).symm.trans (h0.trans (symAlgGerm_eq F x U hU 0)))
  have hy : (symPow n F).presheaf.map iU.op y = 0 :=
    Subtype.ext (heq.trans (map_zero _))
  refine (TopCat.Presheaf.germ_res_apply (symPow n F).presheaf iU x hW y).symm.trans ?_
  rw [hy, map_zero]

/-- The comparison map `symPowStalkL F x n` is injective. -/
theorem symPowStalkL_injective (n : ℕ) : Function.Injective (symPowStalkL F x n) := by
  refine (injective_iff_map_eq_zero (symPowStalkL F x n)).2 fun t ht => ?_
  obtain ⟨U, hU, y, rfl⟩ := TopCat.Presheaf.exists_germ_eq (symPow n F).presheaf t
  refine germ_eq_zero_of_symMapₛₗ_eq_zero F x n U hU y ?_
  exact (SymPow.symMapₛₗ_coe n (R.germ U x hU).hom (germₛₗ F x U hU) y).symm.trans
    (congrArg Subtype.val ((symPowStalkL_germ F x n U hU y).symm.trans ht))

/-- **The comparison on a product of local sections.** The germ of a product of `n` degree-one
generators goes to the product of the germs. Since such products span the symmetric power
(`SymmetricAlgebra.symmetricPower_eq_span_prod_ι`), this determines the comparison map. -/
theorem symPowStalkL_germ_prod_ι (n : ℕ) (U : Opens X) (hx : x ∈ U)
    (s : Fin n → F.obj (op U)) :
    (symPowStalkL F x n (TopCat.Presheaf.germ (symPow n F).presheaf U x hx
          ⟨∏ i : Fin n, SymmetricAlgebra.ι
              ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) (F.obj (op U)) (s i),
            SymmetricAlgebra.prod_ι_mem _ s⟩) :
        SymmetricAlgebra ↑(R.stalk x) ↑(TopCat.Presheaf.stalk F.presheaf x)) =
      ∏ i : Fin n, SymmetricAlgebra.ι ↑(R.stalk x) ↑(TopCat.Presheaf.stalk F.presheaf x)
        (TopCat.Presheaf.germ F.presheaf U x hx (s i)) := by
  refine (congrArg Subtype.val (symPowStalkL_germ F x n U hx _)).trans ?_
  refine (SymPow.symMapₛₗ_coe n (R.germ U x hx).hom (germₛₗ F x U hx) _).trans ?_
  simp only [map_prod]
  exact Finset.prod_congr rfl fun i _ => SymmetricAlgebra.mapₛₗ_ι _ _ (s i)

/-- The comparison map `symPowStalkL F x n` is surjective. -/
theorem symPowStalkL_surjective (n : ℕ) : Function.Surjective (symPowStalkL F x n) := by
  have hprod : ∀ s : Fin n → ↑(TopCat.Presheaf.stalk F.presheaf x),
      (∏ i : Fin n, SymmetricAlgebra.ι ↑(R.stalk x) ↑(TopCat.Presheaf.stalk F.presheaf x) (s i)) ∈
        Submodule.map
          (SymPow.symmetricPower n ↑(R.stalk x) ↑(TopCat.Presheaf.stalk F.presheaf x)).subtype
          (LinearMap.range (symPowStalkL F x n)) := by
    intro s
    choose U hU t ht using fun i : Fin n => TopCat.Presheaf.exists_germ_eq F.presheaf (s i)
    have hW : x ∈ (⨅ i, U i : Opens X) := by
      have h : x ∈ (↑(⨅ i, U i) : Set X) := by
        rw [Opens.coe_iInf]
        exact Set.mem_iInter.2 hU
      exact h
    refine Submodule.mem_map.2 ⟨symPowStalkL F x n
      (TopCat.Presheaf.germ (symPow n F).presheaf (⨅ i, U i : Opens X) x hW
        ⟨∏ i : Fin n, SymmetricAlgebra.ι
            ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op (⨅ i, U i : Opens X)))
            (F.obj (op (⨅ i, U i : Opens X))) (F.map (homOfLE (iInf_le U i)).op (t i)),
          SymmetricAlgebra.prod_ι_mem _ _⟩), ⟨_, rfl⟩, ?_⟩
    refine (symPowStalkL_germ_prod_ι F x n (⨅ i, U i : Opens X) hW
      (fun i => F.map (homOfLE (iInf_le U i)).op (t i))).trans ?_
    exact Finset.prod_congr rfl fun i _ => congrArg _
      ((TopCat.Presheaf.germ_res_apply F.presheaf (homOfLE (iInf_le U i)) x hW (t i)).trans (ht i))
  have hspan : ∀ q ∈ Submodule.span ↑(R.stalk x)
        (Set.range fun s : Fin n → ↑(TopCat.Presheaf.stalk F.presheaf x) =>
          ∏ i : Fin n, SymmetricAlgebra.ι ↑(R.stalk x)
            ↑(TopCat.Presheaf.stalk F.presheaf x) (s i)),
      q ∈ Submodule.map
        (SymPow.symmetricPower n ↑(R.stalk x) ↑(TopCat.Presheaf.stalk F.presheaf x)).subtype
        (LinearMap.range (symPowStalkL F x n)) := by
    intro q hq
    induction hq using Submodule.span_induction with
    | mem w hw => obtain ⟨s, rfl⟩ := hw; exact hprod s
    | zero => exact Submodule.zero_mem _
    | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
    | smul r a _ ha => exact Submodule.smul_mem _ r ha
  intro z
  obtain ⟨w, hw, hwz⟩ := hspan (z : SymmetricAlgebra ↑(R.stalk x)
    ↑(TopCat.Presheaf.stalk F.presheaf x))
    (by rw [← SymmetricAlgebra.symmetricPower_eq_span_prod_ι]; exact z.2)
  obtain ⟨v, hv⟩ := hw
  exact ⟨v, Subtype.ext ((congrArg Subtype.val hv).trans hwz)⟩

/-- **Symmetric powers commute with stalks.** For a presheaf of modules `F` over a presheaf of
commutative rings `R` on a topological space, the stalk at `x` of the presheaf of sectionwise
symmetric powers `U ↦ Symⁿ_{R(U)}(F(U))` is the `n`-th symmetric power of the stalk `F_x` over
the stalk ring `R_x`. The isomorphism is base change along the germ maps. -/
noncomputable def symPowStalkEquiv (n : ℕ) :
    ↑(TopCat.Presheaf.stalk (symPow n F).presheaf x) ≃ₗ[↑(R.stalk x)]
      SymPow.symmetricPower n ↑(R.stalk x) ↑(TopCat.Presheaf.stalk F.presheaf x) :=
  LinearEquiv.ofBijective (symPowStalkL F x n)
    ⟨symPowStalkL_injective F x n, symPowStalkL_surjective F x n⟩

/-- The underlying linear map of `symPowStalkEquiv F x n` is `symPowStalkL F x n`. -/
@[simp]
theorem symPowStalkEquiv_apply (n : ℕ) (t : ↑(TopCat.Presheaf.stalk (symPow n F).presheaf x)) :
    symPowStalkEquiv F x n t = symPowStalkL F x n t := rfl

/-! ### Transport along a morphism of presheaves of modules which is a stalk isomorphism -/

section StalkMap

variable {P Q : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})}

/-- The map induced on stalks by a morphism of presheaves of modules sends the germ of a section
to the germ of its image. -/
theorem stalkFunctor_map_germ (φ : P ⟶ Q) (U : Opens X) (hx : x ∈ U) (m : P.obj (op U)) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map ((toPresheaf _).map φ)
        (TopCat.Presheaf.germ P.presheaf U x hx m) =
      TopCat.Presheaf.germ Q.presheaf U x hx (φ.app (op U) m) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx ((toPresheaf _).map φ) m

/-- The map induced on stalks by a morphism of presheaves of modules, as a linear map over the
stalk of the presheaf of rings. -/
noncomputable def stalkMapL (φ : P ⟶ Q) :
    ↑(TopCat.Presheaf.stalk P.presheaf x) →ₗ[↑(R.stalk x)]
      ↑(TopCat.Presheaf.stalk Q.presheaf x) where
  toFun m := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map ((toPresheaf _).map φ) m
  map_add' m m' := map_add _ m m'
  map_smul' r m := by
    obtain ⟨U₁, h₁, r₀, hr⟩ := R.exists_germ_eq r
    obtain ⟨U₂, hle, h₂, m₀, hm⟩ := TopCat.Presheaf.exists_le_germ_eq P.presheaf m h₁
    have hr₂ : R.germ U₂ x h₂ (R.map (homOfLE hle).op r₀) = r := by
      rw [TopCat.Presheaf.germ_res_apply]; exact hr
    subst hr₂
    subst hm
    rw [← P.germ_smul x U₂ h₂ _ m₀]
    refine (stalkFunctor_map_germ x φ U₂ h₂ _).trans ?_
    refine Eq.trans (congrArg (fun z : Q.obj (op U₂) =>
      TopCat.Presheaf.germ Q.presheaf U₂ x h₂ z)
      ((φ.app (op U₂)).hom.map_smul
        (R.map (homOfLE hle).op r₀ :
          (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U₂)) m₀)) ?_
    refine Eq.trans (Q.germ_smul x U₂ h₂ _ (φ.app (op U₂) m₀)) ?_
    exact congrArg (fun z : ↑(TopCat.Presheaf.stalk Q.presheaf x) =>
      R.germ U₂ x h₂ (R.map (homOfLE hle).op r₀) • z)
      (stalkFunctor_map_germ x φ U₂ h₂ m₀).symm

/-- `stalkMapL x φ` sends the germ of a section `m` to the germ of `φ m`. -/
@[simp]
theorem stalkMapL_germ (φ : P ⟶ Q) (U : Opens X) (hx : x ∈ U) (m : P.obj (op U)) :
    stalkMapL x φ (TopCat.Presheaf.germ P.presheaf U x hx m) =
      TopCat.Presheaf.germ Q.presheaf U x hx (φ.app (op U) m) :=
  stalkFunctor_map_germ x φ U hx m

/-- A morphism of presheaves of modules which induces an isomorphism on the underlying abelian
group stalks induces a linear equivalence of stalk modules. -/
noncomputable def stalkLinearEquiv (φ : P ⟶ Q)
    (h : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((toPresheaf _).map φ))) :
    ↑(TopCat.Presheaf.stalk P.presheaf x) ≃ₗ[↑(R.stalk x)]
      ↑(TopCat.Presheaf.stalk Q.presheaf x) :=
  letI := h
  LinearEquiv.ofBijective (stalkMapL x φ)
    (ConcreteCategory.bijective_of_isIso (C := AddCommGrpCat.{u})
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map ((toPresheaf _).map φ)))

end StalkMap

/-- **Sheafification does not change stalks**, in the form the module sheafification unit needs:
the underlying morphism of presheaves of abelian groups of
`PresheafOfModules.sheafificationAdjunction α` at `P` is
`CategoryTheory.toSheafify (Opens.grothendieckTopology X) P.presheaf` — this is Mathlib's
`PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app`, which holds by `rfl` — and
that morphism is a stalk isomorphism. This is the hypothesis `stalkLinearEquiv` and
`symPowStalkEquivOfStalkIso` take. -/
theorem isIso_stalkFunctor_map_toSheafify (P : X.Presheaf AddCommGrpCat.{u}) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P)) :=
  TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} P

/-- **The stalk of a sheafification of the sectionwise symmetric powers.** If `φ` exhibits `Q` as
having the same stalks as the presheaf `U ↦ Symⁿ_{R(U)}(F(U))` — which the sheafification unit
does, by `isIso_stalkFunctor_map_toSheafify` — then the stalk of `Q` at `x` is `Symⁿ_{R_x}(F_x)`.

This is the form Stacks Tag 01CH is consumed in: by
`SheafOfModules.symmetricPowerSheafifyIso`, the degree-`n` symmetric power of a sheaf of modules
on a ringed space *is* the sheafification of the sectionwise symmetric powers, so taking `Q` to
be that sheafification and `φ` its unit computes the stalk of `Symⁿ F`. -/
@[ega "II 1.7.4" "partial"]
noncomputable def symPowStalkEquivOfStalkIso (n : ℕ)
    {Q : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
    (φ : symPow n F ⟶ Q)
    (h : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((toPresheaf _).map φ))) :
    ↑(TopCat.Presheaf.stalk Q.presheaf x) ≃ₗ[↑(R.stalk x)]
      SymPow.symmetricPower n ↑(R.stalk x) ↑(TopCat.Presheaf.stalk F.presheaf x) :=
  (stalkLinearEquiv x φ h).symm.trans (symPowStalkEquiv F x n)

/-- The comparison of `symPowStalkEquivOfStalkIso` on a product of local sections: the germ of
the image of a product of `n` degree-one generators goes to the product of the germs. -/
theorem symPowStalkEquivOfStalkIso_germ_prod_ι (n : ℕ)
    {Q : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
    (φ : symPow n F ⟶ Q)
    (h : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((toPresheaf _).map φ)))
    (U : Opens X) (hx : x ∈ U) (s : Fin n → F.obj (op U)) :
    (symPowStalkEquivOfStalkIso F x n φ h (TopCat.Presheaf.germ Q.presheaf U x hx
          (φ.app (op U) ⟨∏ i : Fin n, SymmetricAlgebra.ι
              ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) (F.obj (op U)) (s i),
            SymmetricAlgebra.prod_ι_mem _ s⟩)) :
        SymmetricAlgebra ↑(R.stalk x) ↑(TopCat.Presheaf.stalk F.presheaf x)) =
      ∏ i : Fin n, SymmetricAlgebra.ι ↑(R.stalk x) ↑(TopCat.Presheaf.stalk F.presheaf x)
        (TopCat.Presheaf.germ F.presheaf U x hx (s i)) := by
  refine Eq.trans (congrArg Subtype.val (congrArg (symPowStalkEquiv F x n)
    ((stalkLinearEquiv x φ h).symm_apply_eq.2
      (stalkMapL_germ x φ U hx _).symm))) ?_
  exact symPowStalkL_germ_prod_ι F x n U hx s

end PresheafOfModules

end
