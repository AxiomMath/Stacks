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

/-!
# Flat `O_X`-modules: basic definitions and the forward stalk map of the tensor product

For a ringed space `(X, O_X)` this file sets up the category `Mod(O_X)` of `O_X`-modules
(`OXModule X := SheafOfModules (ringSheaf X)`), the sheaf tensor product `OXModule.tensor` and
its functorial form `OXModule.tensorBy` (Tag 01CB, the sheafification of the presheaf tensor
product), flatness `OXModule.Flat` (Tag 05ND), stalks `OXModule.stalk`, stalkwise flatness, and
the stalk-level `Tor_1` (`OXModule.Tor1Stalk`, `OXModule.Tor1IsZero`).  It proves that
sheafification preserves stalks `O_{X,x}`-linearly (`OXModule.sheafify_stalk_iso`) and builds
the forward map `OXModule.presheafTensorStalkFwd` from the stalk of the presheaf tensor product
to the tensor product of the stalks.

The comment below describes the whole development (Tag 08BQ), which continues in
`FlatModuleSheavesAndStalks.StalkTensor`, `FlatModuleSheavesAndStalks.TorOneAndSkyscraper` and
`FlatModuleSheavesAndStalks.FlatIffTorOne`.
-/

@[expose] public section


/-
# Problem Description

Stacks Tag 08BQ ("Tor measures the deviation of flatness").

Let `(X, O_X)` be a ringed space and let `F` be an `O_X`-module.  Then the
following are equivalent:

1. `F` is a flat `O_X`-module (Tag 05ND); and
2. `Tor_1^{O_X}(F, G) = 0` (the zero `O_X`-module) for every `O_X`-module `G`.

## Background and context

* A ringed space `(X, O_X)` is a topological space `X` together with a *sheaf*
  `O_X` of commutative rings.  We use the genuine ringed space type
  `AlgebraicGeometry.RingedSpace` from Mathlib, whose field `isSheaf` records
  that the structure presheaf is a sheaf.  Thus the objects below are genuinely
  modules over a ringed space, not over an arbitrary presheaf of rings.

* (Definition 1, Tag 01CB) The tensor product `F ⊗_{O_X} G` is the
  *sheafification* of the presheaf `U ↦ F(U) ⊗_{O_X(U)} G(U)`; it is again an
  `O_X`-module, and its formation commutes with taking stalks: for each
  `x ∈ X` one has `(F ⊗_{O_X} G)_x ≅ F_x ⊗_{O_{X,x}} G_x`.

* (Definition 2, Tag 05ND) `F` is *flat* if `G ↦ G ⊗_{O_X} F` is exact.  As
  this functor is always right exact (it has a right adjoint, the sheaf-Hom),
  flatness is equivalent to it preserving monomorphisms; this is the form used
  below in `OXModule.Flat`.

* (Definitions 3, 4, Tags 06YH, 08BP) On the derived category `D(O_X)` there is
  a derived tensor product `- ⊗^{L}_{O_X} G` (computed by K-flat resolutions),
  and `Tor_p^{O_X}(F, G) := H^{-p}(F ⊗^{L}_{O_X} G)`.  In particular
  `Tor_0 = ⊗` and `Tor_p = 0` for `p < 0`.

## Formalization notes

We model `Mod(O_X)` by Mathlib's genuine abelian category `SheafOfModules R`,
where `R := O_X` viewed as a sheaf of rings on the open-cover (Grothendieck)
topology of the underlying space.  This is the actual category of
`O_X`-modules over a genuine ringed space, and it is abelian.

* **Definition 1 (tensor product) is formalized directly** (`OXModule.tensor`
  and the endofunctor `OXModule.tensorBy`): it is the *sheafification* of the
  presheaf tensor product `M.val ⊗ N.val`, where `⊗` is the monoidal structure
  on `PresheafOfModules` and `OXModule.sheafify` is the genuine sheafification
  functor `PresheafOfModules.sheafification`.  This is exactly Tag 01CB.

* **Definition 2 (flatness) is formalized directly** at the sheaf level
  (`OXModule.Flat`): `F` is flat iff the genuine tensor endofunctor
  `- ⊗_{O_X} F` preserves monomorphisms.  This is Definition 2 (using the
  automatic right-exactness of the sheaf tensor product).

* **`Tor_1` here is the stalk-level notion, not the sheaf-level one.**
  `OXModule.Tor1Stalk` is the classical module-theoretic `Tor` over the local
  rings `O_{X,x}` (the categorical `CategoryTheory.Tor` on
  `ModuleCat (O_{X,x})`, where projective resolutions are available), and
  `OXModule.Tor1IsZero F G` says that *every stalk* of `Tor_1(F, G)` vanishes.

  This is **not** the same expression as Definition 4: the genuine sheaf-level
  `Tor_p^{O_X}(F, G) = H^{-p}(F ⊗^{L}_{O_X} G)` *is* available in this
  development, as `Stacks.Cohomology.tor` (Tag 08BP) in
  `StacksFrontier.Topology.Sheaves.Cohomology.DerivedTensor.Tor`, built from the
  derived tensor product of Tag 06YU.

  The two agree, and *that agreement is a theorem proved elsewhere in the
  development*, namely
  `Stacks.SheafOfModules.DerivedTensorStalk.isZero_derivedTensorHomology_iff_forall_isZero_tor`
  in `StacksFrontier/Topology/Sheaves/Cohomology/DerivedTensor/TorFlatness.lean`.
  What this file itself supplies is:

    - `OXModule.stalk_tensor_iso` (Tag 01CB): the stalk of the sheaf tensor
      product is the tensor product of the stalks;
    - `OXModule.flat_iff_flat_stalk` (Tag 05NE): sheaf-level flatness (Def 2)
      is equivalent to stalk-wise flatness.

  `OXModule.tor1IsZero_iff_stalk` is **not** a correctness lemma tying the two
  notions together: it is `Iff.rfl`, i.e. it merely unfolds `Tor1IsZero` to its
  own definition, and it carries no mathematical content.

  Consequently `OXModule.flat_iff_tor1_eq_zero` below is the *stalk-level*
  reading of Tag 08BQ: `F` is flat (Def 2) iff all stalks of `Tor_1(F, G)`
  vanish, for every `O_X`-module `G`.  The tag's own statement — with
  `Stacks.Cohomology.tor X 1 F G` on the right-hand side — is
  `Stacks.Cohomology.flat_iff_forall_isZero_tor` in `StacksFrontier/Topology/Sheaves/Cohomology/DerivedTensor/TorFlatness.lean`, obtained
  from the stalk-level reading by that identification, whose own missing
  ingredient was `Stacks.DerivedTensor.homologyIsoTor`
  (`StacksFrontier/Homology/Tor/DerivedTensorTor.lean`): `H^{-p}` of the derived
  tensor product of two modules over a commutative ring is their `Tor_p`.

* **No further hypotheses.** No Noetherian, coherence, or finiteness
  assumptions are made on `X`, `O_X`, `F`, or `G`.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TopCat

universe u

namespace OXModule

variable (X : AlgebraicGeometry.RingedSpace.{u, u})

/-- The structure sheaf `O_X` of a ringed space, viewed as a *sheaf* of rings on
the open-cover (Grothendieck) topology of the underlying space.  Forgetting
commutativity preserves the sheaf condition (`Presheaf.isSheaf_iff_isSheaf_comp`),
so this is a genuine `Sheaf _ RingCat`. -/
@[ega "0 4.1.1"]
noncomputable def ringSheaf : Sheaf (Opens.grothendieckTopology X.carrier) RingCat.{u} :=
  ⟨X.presheaf ⋙ forget₂ CommRingCat RingCat,
    (Presheaf.isSheaf_iff_isSheaf_comp (Opens.grothendieckTopology X.carrier) X.presheaf
      (forget₂ CommRingCat RingCat)).mp X.IsSheaf⟩

/-- The category `Mod(O_X)` of `O_X`-modules, modelled by Mathlib's genuine
abelian category `SheafOfModules` over the structure sheaf of rings.  This is
the abelian category of modules over the *ringed space* `(X, O_X)`. -/
@[sga "2 I 1.7" "partial",
  sga "4 II 6.7" "special case",
  sga "4 IV 11.1.2" "special case",
  sga "4 V 3.5" "special case",
  sga "4 V 6.13" "special case",
  sga "4 Vbis 2.4.0" "partial",
  sga "6 II 2.0" "Mod for a ringed space",
  sga "6 II 2.3.2" "Mod(S), special case",
  sga "6 III 5.1" "special case",
  sga "6 IV 2.1" "partial"]
abbrev _root_.OXModule := SheafOfModules (ringSheaf X)

/-- The presheaf-of-modules tensor product (monoidal structure) on modules over
the structure presheaf of rings; this exists because the base ring presheaf is
of the form `O_X ⋙ forget₂ CommRingCat RingCat`. -/
noncomputable instance monoidalPresheafModules :
    MonoidalCategory (PresheafOfModules ((ringSheaf X).obj)) :=
  PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)

variable {X}

noncomputable local instance sectionModule
    (modulePresheaf : PresheafOfModules.{u} (ringSheaf X).obj)
    (openSet : (TopologicalSpace.Opens X.carrier)ᵒᵖ) :
    Module (X.presheaf.obj openSet) (modulePresheaf.obj openSet) :=
  (modulePresheaf.obj openSet).isModule

noncomputable local instance sectionPresheafModule
    (modulePresheaf : PresheafOfModules.{u} (ringSheaf X).obj)
    (openSet : (TopologicalSpace.Opens X.carrier)ᵒᵖ) :
    Module (X.presheaf.obj openSet) ↑(modulePresheaf.presheaf.obj openSet) :=
  (modulePresheaf.obj openSet).isModule

noncomputable local instance stalkModule
    (modulePresheaf : PresheafOfModules.{u} (ringSheaf X).obj) (point : X.carrier) :
    Module (X.presheaf.stalk point) ↑(TopCat.Presheaf.stalk modulePresheaf.presheaf point) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.presheaf) modulePresheaf point

/-- The genuine sheafification functor sending a presheaf of `O_X`-modules to
its associated sheaf of `O_X`-modules.  As `O_X` is already a sheaf of rings,
the comparison map of rings is the identity. -/
@[sga "4 IV 12.4" "A-module structure on aM"]
noncomputable def sheafify : PresheafOfModules ((ringSheaf X).obj) ⥤ OXModule X :=
  PresheafOfModules.sheafification (R₀ := (ringSheaf X).obj) (R := ringSheaf X) (𝟙 _)

/-- **Definition 1 (tensor product of `O_X`-modules — Tag 01CB).**
`M ⊗_{O_X} N` is the sheafification of the presheaf
`U ↦ M(U) ⊗_{O_X(U)} N(U)`, i.e. the sheafification of the presheaf-of-modules
tensor product `M.val ⊗ N.val`. -/
@[ega "0 4.1.5" "special case",
  ega "III 6.5.7" "(ii), special case",
  sga "4 IV 12.12" "special case",
  sga "4 IV 12.7" "special case",
  sga "4 XVII 4.1.6" "special case",
  sga "6 IV 2.6" "special case"]
noncomputable def tensor (M N : OXModule X) : OXModule X :=
  sheafify.obj ((SheafOfModules.forget _).obj M ⊗ (SheafOfModules.forget _).obj N)

/-- **Definition 1, functorial form.**
The endofunctor `- ⊗_{O_X} F` on `Mod(O_X)`: tensoring on the right by `F`,
realised as (forget to presheaf modules) ∘ (presheaf `tensorRight F`) ∘
(sheafify). -/
@[ega "0 4.1.5" "special case",
  ega "III 6.5.7" "(ii), special case",
  sga "4 IV 12.7" "Functor M ↦ M ⊗_{O_X} F",
  sga "4 XVII 4.1.6" "special case",
  sga "6 IV 2.6" "special case"]
noncomputable def tensorBy (F : OXModule X) : OXModule X ⥤ OXModule X :=
  SheafOfModules.forget _ ⋙ MonoidalCategory.tensorRight ((SheafOfModules.forget _).obj F) ⋙
      sheafify

/-- **Definition 2 (flat `O_X`-module — Tag 05ND).**
An `O_X`-module `F` is *flat* if the genuine tensor endofunctor
`- ⊗_{O_X} F` preserves monomorphisms.  Since `- ⊗_{O_X} F` is always right
exact, this is equivalent to exactness, i.e. to Definition 2. -/
@[sga "4 V 1.1" "special case", sga "4½ Etat_0 6.2" "special case"]
def Flat (F : OXModule X) : Prop := (tensorBy F).PreservesMonomorphisms

/-- The stalk `F_x` of an `O_X`-module `F` at a point `x`, as a module over the
stalk `O_{X,x}` of the structure sheaf (Tag 01CB / `PresheafOfModules` stalk
module structure). -/
noncomputable def stalk (M : OXModule X) (x : X.carrier) : ModuleCat.{u} (X.presheaf.stalk x) :=
  letI : Module (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk M.val.presheaf x) :=
    inferInstanceAs (Module (X.presheaf.stalk x)
      ↑(TopCat.Presheaf.stalk
        (id (M.val) : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)).presheaf x))
  ModuleCat.of (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk M.val.presheaf x)

/-- Stalk-wise flatness: `F` is flat at every point, i.e. each stalk `F_x` is a
flat `O_{X,x}`-module.  By Tag 05NE this is equivalent to `Flat`. -/
@[ega "0 6.7.1" "special case", ega "IV 2.1.1"]
def FlatStalkwise (F : OXModule X) : Prop :=
  ∀ x : X.carrier, Module.Flat (X.presheaf.stalk x) (stalk F x)

/-- **Definition 4 (`Tor_1` — Tag 08BP), stalk-wise form.**
The first Tor of `F` and `G` at a point `x`, computed as the genuine classical
module-theoretic `Tor_1` over the local ring `O_{X,x}` of the stalks `F_x` and
`G_x`.  By Tag 01CB / Tag 05NE this is the stalk at `x` of the sheaf
`Tor_1^{O_X}(F, G)`. -/
noncomputable def Tor1Stalk (F G : OXModule X) (x : X.carrier) :
    ModuleCat.{u} (X.presheaf.stalk x) :=
  ((Tor (ModuleCat.{u} (X.presheaf.stalk x)) 1).obj (stalk F x)).obj (stalk G x)

/-- The statement "`Tor_1^{O_X}(F, G)` is the zero `O_X`-module", expressed
stalk-wise: every stalk of `Tor_1^{O_X}(F, G)` is the zero module.  By Tag 01CB
a sheaf is the zero `O_X`-module exactly when all its stalks vanish. -/
def Tor1IsZero (F G : OXModule X) : Prop := ∀ x : X.carrier, IsZero (Tor1Stalk F G x)

/-- Germ-level injectivity of the stalk map induced by a locally injective
morphism of `AddCommGrp`-valued presheaves on the open-cover site. -/
theorem stalkMap_injective_of_isLocallyInjective
    {Y : TopCat.{u}} {F G : TopCat.Presheaf AddCommGrpCat.{u} Y}
    (f : F ⟶ G) (y : Y) [Presheaf.IsLocallyInjective (Opens.grothendieckTopology Y) f] :
    Function.Injective ((TopCat.Presheaf.stalkFunctor _ y).map f) := by
  intro s t hst
  obtain ⟨U, hxU, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq (x := y) F s
  obtain ⟨V, hxV, b, rfl⟩ := TopCat.Presheaf.exists_germ_eq (x := y) F t
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
    TopCat.Presheaf.stalkFunctor_map_germ_apply] at hst
  obtain ⟨W, hxW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq G y hxU hxV _ _ hst
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← f.naturality, ← f.naturality, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply] at hW
  have hcov := Presheaf.IsLocallyInjective.equalizerSieve_mem
    (J := Opens.grothendieckTopology Y) (φ := f) _ _ hW
  obtain ⟨V', g, hg, hxV'⟩ := Exists.imp (fun a a_1 => a_1) (hcov y hxW)
  rw [← TopCat.Presheaf.germ_res_apply F (g ≫ iU) y hxV' a,
    ← TopCat.Presheaf.germ_res_apply F (g ≫ iV) y hxV' b]
  congr 1
  simp only [Presheaf.equalizerSieve] at hg
  rw [op_comp, op_comp, F.map_comp, F.map_comp, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply]
  exact hg

/-- Germ-level surjectivity of the stalk map induced by a locally surjective
morphism of `AddCommGrp`-valued presheaves on the open-cover site. -/
theorem stalkMap_surjective_of_isLocallySurjective
    {Y : TopCat.{u}} {F G : TopCat.Presheaf AddCommGrpCat.{u} Y}
    (f : F ⟶ G) (y : Y) [Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y) f] :
    Function.Surjective ((TopCat.Presheaf.stalkFunctor _ y).map f) := by
  intro t
  obtain ⟨U, hxU, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq (x := y) G t
  have hcov := Presheaf.IsLocallySurjective.imageSieve_mem
    (J := Opens.grothendieckTopology Y) (f := f) a
  obtain ⟨V, g, hg, hxV⟩ := Exists.imp (fun a a_1 => a_1) (hcov y hxU)
  simp only [Presheaf.imageSieve] at hg
  obtain ⟨b, hb⟩ := hg
  refine ⟨F.germ V y hxV b, ?_⟩
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, hb, TopCat.Presheaf.germ_res_apply]

/-- The sheafification unit `P ⟶ (restrictScalars).obj (sheafify P)` as a morphism
of presheaves of modules; its components are `O_X(U)`-linear. -/
noncomputable def sheafifyUnitHom (P : PresheafOfModules.{u} ((ringSheaf X).obj)) :
    P ⟶ (PresheafOfModules.restrictScalars (𝟙 _)).obj
      ((SheafOfModules.forget (ringSheaf X)).obj (sheafify.obj P)) :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app P

/-- The underlying `AddCommGrp`-valued presheaf morphism of the sheafification
unit; by `toPresheaf_map_sheafificationAdjunction_unit_app` it is `toSheafify`. -/
noncomputable def sheafifyUnitPshMap (P : PresheafOfModules.{u} ((ringSheaf X).obj)) :
    P.presheaf ⟶ (sheafify.obj P).val.presheaf :=
  (PresheafOfModules.toPresheaf _).map
    ((PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app P)

theorem sheafifyUnitPshMap_eq_toSheafify
    (P : PresheafOfModules.{u} ((ringSheaf X).obj)) :
    sheafifyUnitPshMap P =
      CategoryTheory.toSheafify (Opens.grothendieckTopology X.carrier) P.presheaf := by
  exact PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app
    (𝟙 (ringSheaf X).obj) P

instance (P : PresheafOfModules.{u} ((ringSheaf X).obj)) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology X.carrier)
      (sheafifyUnitPshMap P) := by
  rw [sheafifyUnitPshMap_eq_toSheafify]
  exact ((Opens.grothendieckTopology X.carrier).W_toSheafify P.presheaf).isLocallyInjective

instance (P : PresheafOfModules.{u} ((ringSheaf X).obj)) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
      (sheafifyUnitPshMap P) := by
  rw [sheafifyUnitPshMap_eq_toSheafify]
  exact ((Opens.grothendieckTopology X.carrier).W_toSheafify P.presheaf).isLocallySurjective

/-- The component-level `O_X(U)`-linearity of the sheafification unit, transported
to its `AddCommGrp`-valued underlying presheaf morphism. -/
theorem sheafifyUnit_app_smul (P : PresheafOfModules.{u} ((ringSheaf X).obj))
    (W : (TopologicalSpace.Opens X.carrier)ᵒᵖ)
    (s : (ringSheaf X).obj.obj W) (a : P.obj W) :
    (ConcreteCategory.hom ((sheafifyUnitPshMap P).app W)) (s • a)
      = s • (ConcreteCategory.hom ((sheafifyUnitPshMap P).app W)) a := by
  have heq : (ConcreteCategory.hom ((sheafifyUnitPshMap P).app W))
      = (ConcreteCategory.hom ((sheafifyUnitHom P).app W)).toAddMonoidHom := rfl
  rw [heq]
  show (ConcreteCategory.hom ((sheafifyUnitHom P).app W)) (s • a)
      = s • (ConcreteCategory.hom ((sheafifyUnitHom P).app W)) a
  exact map_smul _ _ _

/-- The forward `O_{X,x}`-linear stalk map induced by the sheafification unit:
`(stalk P)_x ⟶ (stalk (sheafify P).val)_x`.  Linearity is `germ_smul` plus the
component-level linearity of the unit. -/
noncomputable def sheafifyStalkFwd (x : X.carrier)
    (P : PresheafOfModules.{u} ((ringSheaf X).obj)) :
    ↑(TopCat.Presheaf.stalk P.presheaf x) →ₗ[X.presheaf.stalk x]
      ↑(TopCat.Presheaf.stalk (sheafify.obj P).val.presheaf x) where
  toFun := (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor _ x).map (sheafifyUnitPshMap P)))
  map_add' left right := map_add
    (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor _ x).map (sheafifyUnitPshMap P)))
    left right
  map_smul' scalar element := by
    let linearMap : ↑(TopCat.Presheaf.stalk P.presheaf x) →ₗ[X.presheaf.stalk x]
        ↑(TopCat.Presheaf.stalk (sheafify.obj P).val.presheaf x) :=
      Stacks.Modules.stalkLinearMap (O := X.presheaf) (z := x) (G := P)
        (H := (PresheafOfModules.restrictScalars (𝟙 (ringSheaf X).obj)).obj (sheafify.obj P).val)
        ((PresheafOfModules.sheafificationAdjunction (R := ringSheaf X) (𝟙 _)).unit.app P)
    exact linearMap.map_smul scalar element

/-- The forward stalk map is an `O_{X,x}`-linear isomorphism, since the underlying
`AddCommGrp` stalk map is bijective (local injectivity + surjectivity of the
sheafification unit). -/
noncomputable def sheafifyStalkLinearEquiv (x : X.carrier)
    (P : PresheafOfModules.{u} ((ringSheaf X).obj)) :
    ↑(TopCat.Presheaf.stalk P.presheaf x) ≃ₗ[X.presheaf.stalk x]
      ↑(TopCat.Presheaf.stalk (sheafify.obj P).val.presheaf x) :=
  LinearEquiv.ofBijective (sheafifyStalkFwd x P)
    ⟨stalkMap_injective_of_isLocallyInjective (sheafifyUnitPshMap P) x,
      stalkMap_surjective_of_isLocallySurjective (sheafifyUnitPshMap P) x⟩

/-- **Sheafification preserves stalks (generic, `O_{X,x}`-linear).**
For any presheaf of modules `P`, the stalk of its sheafification is canonically
isomorphic (as `O_{X,x}`-module) to the stalk of `P`.  This is the generic form
of Tag 01CB's "sheafification commutes with stalks". -/
noncomputable def sheafify_stalk_iso (x : X.carrier)
    (P : PresheafOfModules.{u} ((ringSheaf X).obj)) :
    (sheafify.obj P).stalk x ≅
      ModuleCat.of (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk P.presheaf x) :=
  (sheafifyStalkLinearEquiv x P).symm.toModuleIso

/-! ## Correctness lemmas tying the formalization to the original definitions -/

/-! ### Part (2) of Tag 01CB: presheaf-tensor stalk = tensor of stalks

The remaining content of `stalk_tensor_iso` after sheafification has been peeled
off (`sheafify_stalk_iso`) is the *presheaf*-level statement

  `Presheaf.stalk (M.val ⊗ N.val).presheaf x  ≅  M.stalk x ⊗_{O_{X,x}} N.stalk x`,

i.e. `colim_{U∋x} (M(U) ⊗_{O(U)} N(U)) ≅ (colim M(U)) ⊗_{O_{X,x}} (colim N(U))`.

The strategy builds a
forward `O_{X,x}`-linear map `Φ` (germ `m ⊗ n ↦ germ m ⊗ germ n`, via a cocone
`colimit.desc`) and an inverse `Ψ` (a balanced map sending `germ_U m ⊗ germ_V n`
to `germ_{U⊓V} (m|_{U⊓V} ⊗ n|_{U⊓V})`, via `TensorProduct.lift`), and checks
`Φ ∘ Ψ = id`, `Ψ ∘ Φ = id`.  The decisive technical point (varying base ring):
each scalar `r ∈ O_{X,x}` is a germ `germ_W s` of an honest `s ∈ O_X(W)`, so all
balancing/`smul` identities reduce, via `PresheafOfModules.germ_smul`, to the
*fixed*-ring tensor identities at a common finite stage `W`.

We isolate the four leaf obligations (the two maps + the two round-trip
identities) as separate lemmas; the assembling `def` `presheafTensor_stalk_iso`
is `LinearEquiv.ofLinear` + `LinearEquiv.toModuleIso`.

Those four leaves are proved: `collectAxioms` on both
`OXModule.presheafTensor_stalk_iso` and `OXModule.stalk_tensor_iso` reports
exactly `[propext, Classical.choice, Quot.sound]`, so this development is
complete.

It is still not the right tool for Tag 01CJ, for a reason unrelated to
completeness: it produces a `ModuleCat` isomorphism rather than a `≃ₗ`, and its
sheafified form is a bare `Nonempty` with no germ formula, whereas 01CJ needs the
comparison pinned on germs. That role is filled by
`PresheafOfModules.tensorSheafStalkEquiv` in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorBifunctorStalk`. **A third
proof of this statement should not be written.** -/

/-- Carrier of the stalk of the presheaf-of-modules tensor product `M.val ⊗ N.val`
at `x` (a module over the stalk ring `O_{X,x}`). -/
abbrev presheafTensorStalkCarrier (M N : OXModule X) (x : X.carrier) : Type u :=
  ↑(TopCat.Presheaf.stalk
    ((SheafOfModules.forget (ringSheaf X)).obj M ⊗
      (SheafOfModules.forget (ringSheaf X)).obj N).presheaf x)

noncomputable def ptsFwd_germM (M : OXModule X) (x : X.carrier) (U : TopologicalSpace.Opens
    X.carrier) (hxU : x ∈ U) :
    M.val.obj (Opposite.op U) →+ ↑(M.stalk x) :=
  ConcreteCategory.hom (TopCat.Presheaf.germ M.val.presheaf U x hxU)

noncomputable def ptsFwd_bilU (M N : OXModule X) (x : X.carrier) (U : TopologicalSpace.Opens
    X.carrier) (hxU : x ∈ U) :
    M.val.obj (Opposite.op U) →+ N.val.obj (Opposite.op U) →+ ↑(M.stalk x ⊗ N.stalk x) where
  toFun m :=
    (TensorProduct.mk (X.presheaf.stalk x) (M.stalk x) (N.stalk x) (ptsFwd_germM M x U hxU
        m)).toAddMonoidHom.comp
      (ptsFwd_germM N x U hxU)
  map_zero' := AddMonoidHom.ext fun element =>
    (congrArg (fun (value : M.stalk x) =>
        value ⊗ₜ[X.presheaf.stalk x] ptsFwd_germM N x U hxU element)
      (map_zero (ptsFwd_germM M x U hxU))).trans (TensorProduct.zero_tmul _ _)
  map_add' left right := AddMonoidHom.ext fun element =>
    (congrArg (fun (value : M.stalk x) =>
        value ⊗ₜ[X.presheaf.stalk x] ptsFwd_germM N x U hxU element)
      (map_add (ptsFwd_germM M x U hxU) left right)).trans (TensorProduct.add_tmul _ _ _)

noncomputable def ptsFwd_phiU (M N : OXModule X) (x : X.carrier) (U : TopologicalSpace.Opens
    X.carrier) (hxU : x ∈ U) :
    (TensorProduct (X.presheaf.obj (Opposite.op U))
      (M.val.obj (Opposite.op U)) (N.val.obj (Opposite.op U))) →+ ↑(M.stalk x ⊗ N.stalk x) :=
  TensorProduct.liftAddHom (ptsFwd_bilU M N x U hxU) (by
    intro r m n
    exact (congrArg
      (fun (value : M.stalk x) => value ⊗ₜ[X.presheaf.stalk x] ptsFwd_germM N x U hxU n)
      (PresheafOfModules.germ_smul M.val x U hxU r m)).trans
        ((TensorProduct.smul_tmul (R := ↑(X.presheaf.stalk x))
          (X.presheaf.germ U x hxU r)
          (ptsFwd_germM M x U hxU m) (ptsFwd_germM N x U hxU n)).trans
          (congrArg (fun (value : N.stalk x) =>
              ptsFwd_germM M x U hxU m ⊗ₜ[X.presheaf.stalk x] value)
            (PresheafOfModules.germ_smul N.val x U hxU r n)).symm))

noncomputable def ptsFwd_phiUhom (M N : OXModule X) (x : X.carrier) (U : TopologicalSpace.Opens
    X.carrier) (hxU : x ∈ U) :
    ((SheafOfModules.forget (ringSheaf X)).obj M ⊗ (SheafOfModules.forget (ringSheaf X)).obj
        N).presheaf.obj (Opposite.op U)
      ⟶ AddCommGrpCat.of ↑(M.stalk x ⊗ N.stalk x) :=
  AddCommGrpCat.ofHom (ptsFwd_phiU M N x U hxU)

theorem ptsFwd_phiU_compat (M N : OXModule X) (x : X.carrier)
    (U V : TopologicalSpace.Opens X.carrier) (hxU : x ∈ U) (hxV : x ∈ V) (hVU : V ≤ U)
    (t : ((SheafOfModules.forget (ringSheaf X)).obj M ⊗ (SheafOfModules.forget (ringSheaf X)).obj
        N).presheaf.obj (Opposite.op U)) :
    ptsFwd_phiU M N x V hxV
        (ConcreteCategory.hom
          (((SheafOfModules.forget (ringSheaf X)).obj M ⊗ (SheafOfModules.forget (ringSheaf X)).obj
              N).presheaf.map
            (CategoryTheory.homOfLE hVU).op) t)
      = ptsFwd_phiU M N x U hxU t := by
  let restriction :
      (TensorProduct (X.presheaf.obj (Opposite.op U))
      (M.val.obj (Opposite.op U)) (N.val.obj (Opposite.op U))) →+
        (TensorProduct (X.presheaf.obj (Opposite.op V))
      (M.val.obj (Opposite.op V)) (N.val.obj (Opposite.op V))) :=
    ConcreteCategory.hom ((M.val ⊗ N.val).presheaf.map (homOfLE hVU).op)
  show ptsFwd_phiU M N x V hxV (restriction t) = ptsFwd_phiU M N x U hxU t
  induction t using TensorProduct.induction_on with
  | zero =>
      exact (congrArg (ptsFwd_phiU M N x V hxV) (map_zero restriction)).trans
        ((map_zero (ptsFwd_phiU M N x V hxV)).trans
          (map_zero (ptsFwd_phiU M N x U hxU)).symm)
  | add left right left_eq right_eq =>
      exact (congrArg (ptsFwd_phiU M N x V hxV) (map_add restriction left right)).trans
        ((map_add (ptsFwd_phiU M N x V hxV) _ _).trans
          ((congrArg₂ (· + ·) left_eq right_eq).trans
            (map_add (ptsFwd_phiU M N x U hxU) left right).symm))
  | tmul left right =>
      exact (congrArg (ptsFwd_phiU M N x V hxV)
        (PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul (M₁ := M.val) (M₂ := N.val)
          (homOfLE hVU).op left right)).trans
            (congrArg₂ (fun (leftGerm : M.stalk x) (rightGerm : N.stalk x) =>
              leftGerm ⊗ₜ[X.presheaf.stalk x] rightGerm)
              (TopCat.Presheaf.germ_res_apply M.val.presheaf (homOfLE hVU) x hxV left)
              (TopCat.Presheaf.germ_res_apply N.val.presheaf (homOfLE hVU) x hxV right))

noncomputable def ptsFwd_fwdCocone (M N : OXModule X) (x : X.carrier) :
    CategoryTheory.Limits.Cocone
      ((TopologicalSpace.OpenNhds.inclusion x).op ⋙
        ((SheafOfModules.forget (ringSheaf X)).obj M ⊗ (SheafOfModules.forget (ringSheaf X)).obj
            N).presheaf) where
  pt := AddCommGrpCat.of ↑(M.stalk x ⊗ N.stalk x)
  ι :=
    { app := fun U => ptsFwd_phiUhom M N x U.unop.1 U.unop.2
      naturality := by
        intro U V i
        ext t
        simp only [Functor.comp_obj, Functor.const_obj_obj, Functor.comp_map,
          Functor.const_obj_map]
        exact ptsFwd_phiU_compat M N x U.unop.1 V.unop.1 U.unop.2 V.unop.2 (CategoryTheory.leOfHom
            i.unop) t }

noncomputable def ptsFwd_presheafTensorStalkFwdAdd (M N : OXModule X) (x : X.carrier) :
    presheafTensorStalkCarrier M N x →+ ↑(M.stalk x ⊗ N.stalk x) :=
  AddCommGrpCat.Hom.hom (CategoryTheory.Limits.colimit.desc _ (ptsFwd_fwdCocone M N x))

theorem ptsFwd_fwdAdd_germ (M N : OXModule X) (x : X.carrier) (U : TopologicalSpace.Opens
    X.carrier) (hxU : x ∈ U)
    (t : ((SheafOfModules.forget (ringSheaf X)).obj M ⊗ (SheafOfModules.forget (ringSheaf X)).obj
        N).presheaf.obj (Opposite.op U)) :
    ptsFwd_presheafTensorStalkFwdAdd M N x
        (ConcreteCategory.hom
          (TopCat.Presheaf.germ
            ((SheafOfModules.forget (ringSheaf X)).obj M ⊗ (SheafOfModules.forget (ringSheaf
                X)).obj N).presheaf U x hxU) t)
      = ptsFwd_phiU M N x U hxU t := by
  have key := CategoryTheory.Limits.colimit.ι_desc (ptsFwd_fwdCocone M N x) (Opposite.op ⟨U, hxU⟩)
  have happ := ConcreteCategory.congr_hom key t
  exact happ

theorem ptsFwd_phiU_smul (M N : OXModule X) (x : X.carrier) (U : TopologicalSpace.Opens X.carrier)
    (hxU : x ∈ U)
    (s : X.presheaf.obj (Opposite.op U))
    (t : TensorProduct (X.presheaf.obj (Opposite.op U))
      (M.val.obj (Opposite.op U)) (N.val.obj (Opposite.op U))) :
    ptsFwd_phiU M N x U hxU (s • t)
      = (ConcreteCategory.hom (X.presheaf.germ U x hxU)) s • ptsFwd_phiU M N x U hxU t := by
  induction t using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add a b ha hb => rw [smul_add, map_add, map_add, ha, hb, smul_add]
  | tmul m n =>
      exact (congrArg (ptsFwd_phiU M N x U hxU) (TensorProduct.smul_tmul' s m n)).trans
        ((congrArg (fun (value : M.stalk x) =>
            value ⊗ₜ[X.presheaf.stalk x] ptsFwd_germM N x U hxU n)
          (PresheafOfModules.germ_smul M.val x U hxU s m)).trans
            (TensorProduct.smul_tmul' (R := ↑(X.presheaf.stalk x))
              (X.presheaf.germ U x hxU s)
              (ptsFwd_germM M x U hxU m) (ptsFwd_germM N x U hxU n)).symm)

/-- **Leaf (2a) — forward map `Φ`.**  The `O_{X,x}`-linear map
`colim_{U∋x}(M(U) ⊗_{O(U)} N(U)) → M_x ⊗_{O_{X,x}} N_x` defined on a germ of a
simple tensor by `germ_U(m ⊗ n) ↦ germ_U(m) ⊗ germ_U(n)`.

Construction (informal proof §1): a cocone `(φ_U)` where each `φ_U` is
`TensorProduct.lift` of the `O_X(U)`-balanced biadditive map
`(m,n) ↦ germ_U m ⊗ germ_U n` (balancing via `PresheafOfModules.germ_smul`),
glued by `colimit.desc`; `O_{X,x}`-linearity via `germ_smul` again. -/
noncomputable def presheafTensorStalkFwd (M N : OXModule X) (x : X.carrier) :
    presheafTensorStalkCarrier M N x →ₗ[X.presheaf.stalk x]
      (M.stalk x ⊗ N.stalk x : ModuleCat.{u} (X.presheaf.stalk x)) where
  toFun := ptsFwd_presheafTensorStalkFwdAdd M N x
  map_add' left right := map_add (ptsFwd_presheafTensorStalkFwdAdd M N x) left right
  map_smul' := by
    intro r z
    simp only [RingHom.id_apply]
    obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq (x := x) X.presheaf r
    obtain ⟨V, hxV, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq (x := x)
      ((SheafOfModules.forget (ringSheaf X)).obj M ⊗ (SheafOfModules.forget (ringSheaf X)).obj
          N).presheaf z
    have hxW : x ∈ U ⊓ V := ⟨hxU, hxV⟩
    -- restrict s and t to W = U ⊓ V
    have hs : (ConcreteCategory.hom (X.presheaf.germ U x hxU)) s
        = (ConcreteCategory.hom (X.presheaf.germ (U ⊓ V) x hxW))
            ((ConcreteCategory.hom (X.presheaf.map (homOfLE inf_le_left).op)) s) := by
      rw [TopCat.Presheaf.germ_res_apply]
    have ht : (ConcreteCategory.hom (TopCat.Presheaf.germ
            ((SheafOfModules.forget (ringSheaf X)).obj M ⊗ (SheafOfModules.forget (ringSheaf
                X)).obj N).presheaf V x hxV)) t
        = (ConcreteCategory.hom (TopCat.Presheaf.germ
            ((SheafOfModules.forget (ringSheaf X)).obj M ⊗ (SheafOfModules.forget (ringSheaf
                X)).obj N).presheaf (U ⊓ V) x hxW))
            ((ConcreteCategory.hom
              (((SheafOfModules.forget (ringSheaf X)).obj M
                ⊗ (SheafOfModules.forget (ringSheaf X)).obj N).presheaf.map
                  (homOfLE inf_le_right).op)) t) := by
      rw [TopCat.Presheaf.germ_res_apply]
    rw [hs, ht]
    let restrictedScalar : X.presheaf.obj (Opposite.op (U ⊓ V)) :=
      (ConcreteCategory.hom (X.presheaf.map (homOfLE inf_le_left).op)) s
    let restrictedTensor : (M.val ⊗ N.val).obj (Opposite.op (U ⊓ V)) := (ConcreteCategory.hom
      ((M.val ⊗ N.val).presheaf.map (homOfLE inf_le_right).op)) t
    exact (congrArg (ptsFwd_presheafTensorStalkFwdAdd M N x)
      (PresheafOfModules.germ_smul (M.val ⊗ N.val) x (U ⊓ V) hxW
        restrictedScalar restrictedTensor).symm).trans
      ((ptsFwd_fwdAdd_germ M N x (U ⊓ V) hxW (restrictedScalar • restrictedTensor)).trans
        ((ptsFwd_phiU_smul M N x (U ⊓ V) hxW restrictedScalar restrictedTensor).trans
          (congrArg (fun value => X.presheaf.germ (U ⊓ V) x hxW restrictedScalar • value)
            (ptsFwd_fwdAdd_germ M N x (U ⊓ V) hxW restrictedTensor)).symm))

end OXModule
