module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Sites.LocalSite
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
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Sheafify
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

attribute [local implicit_reducible] PresheafOfModules.presheaf
  PresheafOfModules.tensorObj PresheafOfModules.tensorHom
  AlgebraicGeometry.SheafedSpace.sheaf
  TopCat.Sheaf
  PresheafOfModules.ofPresheaf ModuleCat.restrictScalars
  TopologicalSpace.OpenNhds TopologicalSpace.OpenNhds.inclusion

/-
# Problem Description (Stacks Project Tag 01CB, "Stalk of tensor product")

Let `(X, O_X)` be a ringed space (a topological space `X` together with a sheaf of
commutative rings `O_X`), and let `F`, `G` be sheaves of `O_X`-modules.  Fix a point
`x : X`.

## Main Definitions
1. *Stalk of a sheaf at a point.*  For a sheaf `H` on `X`, the stalk `H_x` is the
   filtered colimit `H_x = colim_{x ∈ U} H(U)` over the directed system of open
   neighbourhoods `U` of `x` (ordered by reverse inclusion), with restriction maps as
   transition maps.
2. *Stalk of the structure sheaf and module structure.*  The stalk `O_{X,x}` is a
   commutative ring, and for each `O_X`-module `F` the stalk `F_x` is naturally a
   module over `O_{X,x}`, induced from the `O_X(U)`-module structures on `F(U)` by
   passing to the colimit.
3. *Tensor product of `O_X`-modules.*  `F ⊗_{O_X} G` is the `O_X`-module obtained by
   sheafifying the presheaf `U ↦ F(U) ⊗_{O_X(U)} G(U)` (Stacks Tag 01CA).

## Main Statements
1. (Stalk of a tensor product.)  There is a canonical isomorphism of `O_{X,x}`-modules
   `(F ⊗_{O_X} G)_x ≅ F_x ⊗_{O_{X,x}} G_x`.
2. (Functoriality.)  This isomorphism is natural in both `F` and `G`.

## Notes on the formalization

We use Mathlib's genuine sheaf-theoretic infrastructure throughout.

* `X : AlgebraicGeometry.RingedSpace` is an actual ringed space;
  `X.presheaf : TopCat.Presheaf CommRingCat X.carrier` is the sheaf of commutative
  rings `O_X`, and `x : X.carrier` is a point.
* `O_X`-modules are `PresheafOfModules`/`SheafOfModules` over the structure sheaf
  `O X := X.presheaf ⋙ forget₂ CommRingCat RingCat`, viewed as a `Sheaf J RingCat` for
  the open-cover Grothendieck topology `J` on `Opens X` (`structureSheafRing`).
* The presheaf tensor product `U ↦ F(U) ⊗_{O_X(U)} G(U)` is built as a genuine
  `PresheafOfModules` (`PresheafOfModules.tensorObj`), and the tensor product of sheaves of modules
  `F ⊗_{O_X} G` (Stacks Tag 01CA) is its sheafification `tensorSheaf`, obtained via
  `PresheafOfModules.sheafification`.  The comparison map on sections
  `F(U) ⊗_{O_X(U)} G(U) → (F ⊗_{O_X} G)(U)` is the unit of the sheafification
  adjunction (`toTensorSheafSection`).

### Stalks and the canonical `O_{X,x}`-module structure

The stalk `O_{X,x}` of the structure sheaf is the genuine `X.presheaf.stalk x`, a
commutative ring (`ringStalk`).  For an `O_X`-module `F`, the underlying abelian group of
the stalk `F_x` is the genuine Mathlib sheaf stalk `grpStalk X F x = (F.presheaf).stalk x`,
the filtered colimit `colim_{x∈U} F(U)`.  The germ maps `grpGerm : F(U) → F_x` are the
genuine `TopCat.Presheaf.germ`.

The canonical `O_{X,x}`-module structure on `F_x` is Mathlib's colimit module structure on
the stalk of a presheaf of modules (`Mathlib.Algebra.Category.ModuleCat.Stalk`), seated at this
spelling as the instance `stalkModule`.  Its characterising property
`stalkModule_germ_smul`, `germ (r • m) = (germ r) • (germ m)`, is Mathlib's
`PresheafOfModules.germ_smul`.
-/

open CategoryTheory TensorProduct

namespace Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

variable (X : AlgebraicGeometry.RingedSpace.{u, u})

/-! ### The structure sheaf as a presheaf/sheaf of rings. -/

/-- The structure sheaf `O_X`, viewed as a presheaf of (not necessarily commutative)
rings, so that we may speak of `PresheafOfModules` over it.  Each section ring
`(O X).obj U = O_X(U)` is in fact commutative. -/
noncomputable abbrev O : (TopologicalSpace.Opens X.carrier)ᵒᵖ ⥤ RingCat.{u} :=
  X.presheaf ⋙ forget₂ CommRingCat RingCat

/-- The open-cover Grothendieck topology on the opens of `X`. -/
abbrev JX : GrothendieckTopology (TopologicalSpace.Opens X.carrier) :=
  Opens.grothendieckTopology X.carrier

/-! ### Stalks at a point `x`. -/

/-- The stalk `O_{X,x}` of the structure sheaf at `x`, a commutative ring. -/
noncomputable abbrev ringStalk (x : X.carrier) : CommRingCat.{u} := X.presheaf.stalk x

/-- The ring germ map `O_X(U) → O_{X,x}`, a ring homomorphism. -/
noncomputable def ringGerm (x : X.carrier) (U : TopologicalSpace.Opens X.carrier) (h : x ∈ U) :
    X.presheaf.obj (Opposite.op U) →+* (ringStalk X x) :=
  (X.presheaf.germ U x h).hom

/-- **The underlying abelian group of the stalk `F_x`**, the genuine Mathlib sheaf stalk
`colim_{x∈U} F(U)` of the underlying presheaf of abelian groups of `F`. -/
noncomputable abbrev grpStalk (F : PresheafOfModules.{u} (O X)) (x : X.carrier) :
    AddCommGrpCat.{u} :=
  TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X.carrier) F.presheaf x

/-- The genuine germ map `F(U) → F_x`, an additive homomorphism. -/
noncomputable def grpGerm (F : PresheafOfModules.{u} (O X)) (x : X.carrier)
    (U : TopologicalSpace.Opens X.carrier) (h : x ∈ U) :
    F.obj (Opposite.op U) →+ (grpStalk X F x) :=
  (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := X.carrier) F.presheaf U x h).hom

/-- The genuine map on stalks `F_x → F'_x` induced by a morphism `φ : F ⟶ F'` of
presheaves of modules (`TopCat.Presheaf.stalkFunctor` of the underlying presheaf
morphism). -/
@[ega "0 3.1.6" "special case"]
noncomputable def stalkMap (F F' : PresheafOfModules.{u} (O X)) (φ : F ⟶ F') (x : X.carrier) :
    (grpStalk X F x) →+ (grpStalk X F' x) :=
  ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((PresheafOfModules.toPresheaf (O X)).map φ)).hom

/-- **The canonical `O_{X,x}`-module structure on the stalk `F_x`.**  This is Mathlib's
colimit module structure on the stalk of a presheaf of modules
(`PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier`), seated at
the `ringStalk`/`grpStalk` spelling; it is that instance by definition, so the two agree at
instance transparency.  It is characterised by `stalkModule_germ_smul` below. -/
noncomputable instance stalkModule (F : PresheafOfModules.{u} (O X)) (x : X.carrier) :
    Module (ringStalk X x) (grpStalk X F x) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.presheaf) F x

/-- **Characterisation of the stalk module structure.**  The germ map is semilinear over
the ring germ: `germ (r • m) = (germ r) • (germ m)`.  This uniquely pins down the
`O_{X,x}`-module structure `stalkModule` (Mathlib's `PresheafOfModules.germ_smul`). -/
theorem stalkModule_germ_smul (F : PresheafOfModules.{u} (O X)) (x : X.carrier)
    (U : TopologicalSpace.Opens X.carrier) (hxU : x ∈ U)
    (r : X.presheaf.obj (Opposite.op U)) (m : F.obj (Opposite.op U)) :
    grpGerm X F x U hxU (r • m)
      = (ringGerm X x U hxU r) • grpGerm X F x U hxU m :=
  PresheafOfModules.germ_smul (R := X.presheaf) F x U hxU r m

/-- The ring germ of a restricted section is the germ of the section. -/
private theorem ringGerm_map (x : X.carrier) {U V : TopologicalSpace.Opens X.carrier}
    (i : U ⟶ V) (hxU : x ∈ U) (hxV : x ∈ V) (s : X.presheaf.obj (Opposite.op V)) :
    ringGerm X x U hxU ((X.presheaf.map i.op).hom s) = ringGerm X x V hxV s :=
  TopCat.Presheaf.germ_res_apply X.presheaf i x hxU s

/-- The stalk germ of a restricted section is the germ of the section. -/
private theorem grpGerm_map (F : PresheafOfModules.{u} (O X)) (x : X.carrier)
    {U V : TopologicalSpace.Opens X.carrier} (i : U ⟶ V) (hxU : x ∈ U) (hxV : x ∈ V)
    (s : F.obj (Opposite.op V)) :
    grpGerm X F x U hxU ((F.map i.op).hom s) = grpGerm X F x V hxV s :=
  TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) F.presheaf i x hxU s

/-! ### The presheaf tensor product `U ↦ F(U) ⊗_{O_X(U)} G(U)` (Tag 01CA). -/

/-- Sheafification of presheaves of `O_X`-modules into sheaves of `O_X`-modules. -/
noncomputable def sheafifyFunctor :
    PresheafOfModules.{u} (O X) ⥤ SheafOfModules.{u} (structureSheafRing X) :=
  PresheafOfModules.sheafification (R := structureSheafRing X) (𝟙 (structureSheafRing X).obj)


/-- The unit of the sheafification adjunction: the canonical morphism from a presheaf of
modules to (the underlying presheaf of) its sheafification. -/
noncomputable def sheafifyUnit (M : PresheafOfModules.{u} (O X)) :
    M ⟶ (SheafOfModules.forget (structureSheafRing X) ⋙
          PresheafOfModules.restrictScalars (𝟙 (structureSheafRing X).obj)).obj
        ((sheafifyFunctor X).obj M) :=
  (PresheafOfModules.sheafificationAdjunction (R := structureSheafRing X)
    (𝟙 (structureSheafRing X).obj)).unit.app M

attribute [local implicit_reducible] sheafifyFunctor sheafifyUnit

/-- The canonical map on sections `F(U) ⊗_{O_X(U)} G(U) → (F ⊗_{O_X} G)(U)` from the
presheaf tensor product into the sheafified tensor product. -/
noncomputable def toTensorSheafSection (F G : SheafOfModules.{u} (structureSheafRing X))
    (U : (TopologicalSpace.Opens X.carrier)ᵒᵖ) :
    TensorProduct (X.presheaf.obj U) (F.val.obj U) (G.val.obj U) →
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj F).obj G)).val.obj U :=
  fun t => ((sheafifyUnit X ((PresheafOfModules.tensorObj (O := X.presheaf) F.val G.val))).app U).hom t

/-! ### Functoriality: the canonical induced morphism `φ ⊗ ψ`. -/







/-- **The induced morphism of a tensor product is functorial.** Sheafification is a functor
and the presheaf-level tensor of morphisms is functorial, so the two composites agree. -/
public theorem tensorSheafMap_comp {A B C D E F : SheafOfModules.{u} (structureSheafRing X)}
    (f : A ⟶ B) (g : B ⟶ C) (h : D ⟶ E) (i : E ⟶ F) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u}))).map ((f, h) : (_, _) ⟶ (_, _))) ≫ ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u}))).map ((g, i) : (_, _) ⟶ (_, _))) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u}))).map (((f ≫ g), (h ≫ i)) : (_, _) ⟶ (_, _)))  := by
  exact ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u}))).map_comp
    ((f, h) : (A, D) ⟶ (B, E)) ((g, i) : (B, E) ⟶ (C, F))).symm

/-! ### Statement 1: the stalk of a tensor product (canonical isomorphism). -/

/-- The canonical `O_{X,x}`-linear stalk map `F_x → F'_x` induced by a morphism
`φ : F ⟶ F'` of presheaves of modules: its underlying additive map is the genuine
`stalkMap`, and its `O_{X,x}`-linearity is the lemma `stalkMap_map_smul`. -/
lemma stalkMap_map_smul (F F' : PresheafOfModules.{u} (O X)) (φ : F ⟶ F') (x : X.carrier)
    (r : ringStalk X x) (m : grpStalk X F x) :
    stalkMap X F F' φ x (r • m) = r • stalkMap X F F' φ x m := by
  -- SANITY CHECK PASSED
  -- Pick representatives for `r` and `m` on a common neighbourhood `U`.
  obtain ⟨Ur, hUr, sr, hsr⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨Um, hUm, sm, hsm⟩ :=
    TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u}) (X := X.carrier) F.presheaf m
  set U : TopologicalSpace.Opens X.carrier := Ur ⊓ Um with hUdef
  set hxU : x ∈ U := ⟨hUr, hUm⟩ with hxUmem
  set iUr : U ⟶ Ur := homOfLE inf_le_left with hiUr
  set iUm : U ⟶ Um := homOfLE inf_le_right with hiUm
  set rU : X.presheaf.obj (Opposite.op U) := (X.presheaf.map iUr.op).hom sr with hrU
  set mU : F.obj (Opposite.op U) := (F.map iUm.op).hom sm with hmU
  -- germ identifications: `ringGerm rU = r`, `grpGerm mU = m`.
  have hgr : ringGerm X x U hxU rU = r := (ringGerm_map X x iUr hxU hUr sr).trans hsr
  have hgm : grpGerm X F x U hxU mU = m := (grpGerm_map X F x iUm hxU hUm sm).trans hsm
  rw [← hgr, ← hgm]
  -- `r • m = grpGerm (rU • mU)`.
  rw [← stalkModule_germ_smul X F x U hxU rU mU]
  -- germ-naturality of `stalkMap` (= stalkFunctor of the underlying presheaf morphism).
  have hnat : ∀ (s : F.obj (Opposite.op U)),
      stalkMap X F F' φ x (grpGerm X F x U hxU s)
        = grpGerm X F' x U hxU ((φ.app (Opposite.op U)).hom s) := by
    intro s
    exact TopCat.Presheaf.stalkFunctor_map_germ_apply' U x hxU
      ((PresheafOfModules.toPresheaf (O X)).map φ) s
  rw [hnat (rU • mU), hnat mU]
  -- `φ.app U` is `O_X(U)`-linear: `φ(rU • mU) = rU • φ(mU)`.
  have hφ : (φ.app (Opposite.op U)).hom (rU • mU)
      = rU • (φ.app (Opposite.op U)).hom mU := (φ.app (Opposite.op U)).hom.map_smul rU mU
  rw [hφ]
  -- and `grpGerm (rU • φ(mU)) = ringGerm rU • grpGerm φ(mU) = r • ...`.
  rw [stalkModule_germ_smul X F' x U hxU rU ((φ.app (Opposite.op U)).hom mU), hgr]

/-- **The canonical `O_{X,x}`-linear stalk map `F_x → F'_x`** induced by a morphism
`φ : F ⟶ F'` of presheaves of modules.  Its underlying additive map is the genuine
`stalkMap`; its `O_{X,x}`-linearity (`map_smul'`) is the lemma `stalkMap_map_smul`. -/
noncomputable def stalkMapL (F F' : PresheafOfModules.{u} (O X)) (φ : F ⟶ F') (x : X.carrier) :
    (grpStalk X F x) →ₗ[ringStalk X x] (grpStalk X F' x) where
  toFun := stalkMap X F F' φ x
  map_add' := (stalkMap X F F' φ x).map_add
  map_smul' := stalkMap_map_smul X F F' φ x

@[simp] lemma stalkMapL_toAddMonoidHom (F F' : PresheafOfModules.{u} (O X)) (φ : F ⟶ F')
    (x : X.carrier) :
    (stalkMapL X F F' φ x).toAddMonoidHom = stalkMap X F F' φ x := rfl

/-- The linear map on module stalks carries germs to germs. -/
lemma stalkMapL_germ (source target : PresheafOfModules.{u} (O X))
    (morphism : source ⟶ target) (point : X.carrier)
    (openSet : TopologicalSpace.Opens X.carrier) (membership : point ∈ openSet)
    (sectionValue : source.obj (.op openSet)) :
    stalkMapL X source target morphism point
        (grpGerm X source point openSet membership sectionValue) =
      grpGerm X target point openSet membership
        ((morphism.app (.op openSet)).hom sectionValue) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply' openSet point membership
    ((PresheafOfModules.toPresheaf (O X)).map morphism) sectionValue

section TensorSheafStalkIso

/-- The underlying additive stalk map of the sheafification unit is an isomorphism: this is
`TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso`, after identifying the underlying
presheaf morphism of the sheafification unit with `toSheafify`. -/
lemma stalkMap_sheafifyUnit_isIso (x : X.carrier)
    (P : PresheafOfModules.{u} (O X)) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf (O X)).map (sheafifyUnit X P))) := by
  rw [sheafifyUnit, PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
  exact TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} P.presheaf

end TensorSheafStalkIso

/-- **(θ) Sheafification preserves stalks (Stacks Tag 007X).**  The stalk of the sheaf
tensor product `tensorSheaf = (PresheafOfModules.tensorObj)^#` is canonically `O_{X,x}`-linearly
isomorphic to the stalk of the presheaf tensor product, and the germ of the image of a
presheaf-tensor section `t` under the sheafification unit (`toTensorSheafSection`) maps to
the germ of `t` itself.

This is the abelian-group statement `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso`
(the stalk functor applied to the sheafification unit is an iso) upgraded to an
`O_{X,x}`-linear equivalence via `stalkModule_germ_smul`. -/
theorem exists_tensorSheafStalkIso (x : X.carrier)
    (F G : SheafOfModules.{u} (structureSheafRing X)) :
    letI := stalkModule X
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj F).obj G).val x
    ∃ θ : (grpStalk X ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj F).obj G)).val x) ≃ₗ[ringStalk X x]
        (grpStalk X ((PresheafOfModules.tensorObj (O := X.presheaf) F.val G.val)) x),
      ∀ (U : TopologicalSpace.Opens X.carrier) (hxU : x ∈ U)
        (t : ((PresheafOfModules.tensorObj (O := X.presheaf) F.val G.val)).obj (Opposite.op U)),
        θ (grpGerm X ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj F).obj G)).val x U hxU
            ((sheafifyUnit X ((PresheafOfModules.tensorObj (O := X.presheaf) F.val G.val))).app (Opposite.op U) t))
          = grpGerm X ((PresheafOfModules.tensorObj (O := X.presheaf) F.val G.val)) x U hxU t := by
  letI := stalkModule X
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj F).obj G).val x
  set P := (PresheafOfModules.tensorObj (O := X.presheaf) F.val G.val) with hP
  -- The `O_{X,x}`-linear stalk map `ι : P_x →ₗ (P^#)_x` induced by the sheafification unit.
  set ι : (grpStalk X P x) →ₗ[ringStalk X x] (grpStalk X ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj F).obj G)).val x) :=
    stalkMapL X P ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj F).obj G)).val (sheafifyUnit X P) x with hι
  -- Its underlying additive map is the genuine `stalkMap`, which is an iso of abelian groups.
  have hiso : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf (O X)).map (sheafifyUnit X P))) :=
    stalkMap_sheafifyUnit_isIso X x P
  -- Hence `ι` is bijective.
  have hbij : Function.Bijective ι :=
    ConcreteCategory.bijective_of_isIso (C := AddCommGrpCat.{u})
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf (O X)).map (sheafifyUnit X P)))
  -- Upgrade `ι` to a linear equivalence `e : P_x ≃ₗ (P^#)_x`.
  set e : (grpStalk X P x) ≃ₗ[ringStalk X x] (grpStalk X ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj F).obj G)).val x) :=
    LinearEquiv.ofBijective ι hbij with he
  -- The germ-naturality of `ι`: `ι (germ_P t) = germ_{P^#} (unit t)`.
  have hgerm : ∀ (U : TopologicalSpace.Opens X.carrier) (hxU : x ∈ U)
      (t : P.obj (Opposite.op U)),
      ι (grpGerm X P x U hxU t)
        = grpGerm X ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj F).obj G)).val x U hxU
            ((sheafifyUnit X P).app (Opposite.op U) t) := by
    intro U hxU t
    exact TopCat.Presheaf.stalkFunctor_map_germ_apply' U x hxU
      ((PresheafOfModules.toPresheaf (O X)).map (sheafifyUnit X P)) t
  -- Take `θ := e.symm` and verify the germ compatibility.
  refine ⟨e.symm, ?_⟩
  intro U hxU t
  rw [LinearEquiv.symm_apply_eq]
  exact (hgerm U hxU t).symm

section PhiProbe

open TopologicalSpace

/-- The biadditive, `O(U)`-balanced map `(m,n) ↦ germ m ⊗ germ n`, lifted to an additive
hom on `F(U) ⊗_{O(U)} G(U)`, valued in `F_x ⊗_{O_x} G_x`.  This is the cocone leg for the
forward map `Φ`. -/
noncomputable def phiLeg (x : X.carrier) (F G : PresheafOfModules.{u} (O X))
    (U : TopologicalSpace.Opens X.carrier) (hxU : x ∈ U) :
    TensorProduct (X.presheaf.obj (Opposite.op U)) (F.obj (Opposite.op U)) (G.obj (Opposite.op U))
      →+ (grpStalk X F x ⊗[ringStalk X x] grpStalk X G x) :=
  TensorProduct.liftAddHom
    (R := X.presheaf.obj (Opposite.op U))
    { toFun := fun m =>
        { toFun := fun n =>
            (grpGerm X F x U hxU m) ⊗ₜ[ringStalk X x] (grpGerm X G x U hxU n)
          map_zero' := by simp
          map_add' := fun n₁ n₂ => by simp [tmul_add] }
      map_zero' := by ext n; simp
      map_add' := fun m₁ m₂ => by ext n; simp [add_tmul] }
    (by
      intro r m n
      change (grpGerm X F x U hxU (r • m)) ⊗ₜ[ringStalk X x] (grpGerm X G x U hxU n)
        = (grpGerm X F x U hxU m) ⊗ₜ[ringStalk X x] (grpGerm X G x U hxU (r • n))
      rw [stalkModule_germ_smul X F x U hxU r m, stalkModule_germ_smul X G x U hxU r n]
      rw [TensorProduct.smul_tmul])

@[simp] lemma phiLeg_tmul (x : X.carrier) (F G : PresheafOfModules.{u} (O X))
    (U : TopologicalSpace.Opens X.carrier) (hxU : x ∈ U)
    (m : F.obj (Opposite.op U)) (n : G.obj (Opposite.op U)) :
    phiLeg X x F G U hxU (m ⊗ₜ[X.presheaf.obj (Opposite.op U)] n)
      = (grpGerm X F x U hxU m) ⊗ₜ[ringStalk X x] (grpGerm X G x U hxU n) :=
  rfl

/-- The forward cocone: legs `phiLeg` assembled into a cocone over the stalk diagram of the
presheaf tensor product, with apex `F_x ⊗ G_x`. -/
noncomputable def phiCocone (x : X.carrier) (F G : PresheafOfModules.{u} (O X)) :
    Limits.Cocone ((OpenNhds.inclusion x).op ⋙ ((PresheafOfModules.tensorObj (O := X.presheaf) F G)).presheaf) where
  pt := AddCommGrpCat.of (grpStalk X F x ⊗[ringStalk X x] grpStalk X G x)
  ι :=
    { app := fun j =>
        AddCommGrpCat.ofHom (phiLeg X x F G ((OpenNhds.inclusion x).obj j.unop) j.unop.2)
      naturality := by
        intro j k f
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro t
        change (phiLeg X x F G ((OpenNhds.inclusion x).obj k.unop) k.unop.2)
            ((((PresheafOfModules.tensorObj (O := X.presheaf) F G)).presheaf.map ((OpenNhds.inclusion x).op.map f)).hom t)
          = (phiLeg X x F G ((OpenNhds.inclusion x).obj j.unop) j.unop.2) t
        induction t using TensorProduct.induction_on with
        | zero => rw [map_zero]; exact (map_zero _).symm
        | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
        | tmul m n =>
            change (grpGerm X F x ((OpenNhds.inclusion x).obj k.unop) k.unop.2)
                  ((F.map ((OpenNhds.inclusion x).op.map f)).hom m)
                ⊗ₜ[ringStalk X x]
                (grpGerm X G x ((OpenNhds.inclusion x).obj k.unop) k.unop.2)
                  ((G.map ((OpenNhds.inclusion x).op.map f)).hom n)
              = (grpGerm X F x ((OpenNhds.inclusion x).obj j.unop) j.unop.2 m)
                ⊗ₜ[ringStalk X x]
                (grpGerm X G x ((OpenNhds.inclusion x).obj j.unop) j.unop.2 n)
            congr 1
            · exact TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) F.presheaf
                ((OpenNhds.inclusion x).op.map f).unop x k.unop.2 m
            · exact TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) G.presheaf
                ((OpenNhds.inclusion x).op.map f).unop x k.unop.2 n }

end PhiProbe

section PhiProbe2
open TopologicalSpace

example (F : PresheafOfModules.{u} (O X)) (x : X.carrier)
    (U : TopologicalSpace.Opens X.carrier) (hxU : x ∈ U) :
    TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) F.presheaf U x hxU
      = Limits.colimit.ι ((OpenNhds.inclusion x).op ⋙ F.presheaf) (Opposite.op ⟨U, hxU⟩) := by
  rfl

/-- The forward map `Φ : grpStalk(PresheafOfModules.tensorObj) → F_x ⊗ G_x`, via the colimit universal
property applied to `phiCocone`. -/
noncomputable def phiHom (x : X.carrier) (F G : PresheafOfModules.{u} (O X)) :
    grpStalk X ((PresheafOfModules.tensorObj (O := X.presheaf) F G)) x
      →+ (grpStalk X F x ⊗[ringStalk X x] grpStalk X G x) :=
  (Limits.colimit.desc _ (phiCocone X x F G)).hom

lemma phiHom_germ (x : X.carrier) (F G : PresheafOfModules.{u} (O X))
    (U : TopologicalSpace.Opens X.carrier) (hxU : x ∈ U)
    (t : TensorProduct (X.presheaf.obj (Opposite.op U)) (F.obj (Opposite.op U))
      (G.obj (Opposite.op U))) :
    phiHom X x F G (grpGerm X ((PresheafOfModules.tensorObj (O := X.presheaf) F G)) x U hxU t)
      = phiLeg X x F G U hxU t := by
  have h := Limits.colimit.ι_desc (phiCocone X x F G) (Opposite.op (⟨U, hxU⟩ : OpenNhds x))
  have h2 := congrArg (fun (m : _ ⟶ _) => (ConcreteCategory.hom m) t) h
  exact h2

end PhiProbe2

section PsiProbe
open TopologicalSpace

/-- For a fixed section `m ∈ F(U)`, the additive map `G(V) →+ PT_x`,
`n ↦ germ_{U⊓V}((m|) ⊗ (n|))`.  This is the inner cocone leg for building the inverse `Ψ`. -/
noncomputable def psiInnerLeg (x : X.carrier) (F G : PresheafOfModules.{u} (O X))
    (U : TopologicalSpace.Opens X.carrier) (hxU : x ∈ U) (m : F.obj (Opposite.op U))
    (V : TopologicalSpace.Opens X.carrier) (hxV : x ∈ V) :
    G.obj (Opposite.op V) →+ grpStalk X ((PresheafOfModules.tensorObj (O := X.presheaf) F G)) x where
  toFun n := grpGerm X ((PresheafOfModules.tensorObj (O := X.presheaf) F G)) x (U ⊓ V) (TopologicalSpace.Opens.mem_inf.mpr ⟨hxU, hxV⟩)
    (((F.restrictₛₗ (homOfLE inf_le_left).op) m)
      ⊗ₜ[X.presheaf.obj (Opposite.op (U ⊓ V))]
      ((G.restrictₛₗ (homOfLE inf_le_right).op) n))
  map_zero' := by
    rw [map_zero, TensorProduct.tmul_zero, map_zero]
  map_add' n₁ n₂ := by
    rw [map_add, TensorProduct.tmul_add, map_add]

/-- The inner cocone over `G`'s stalk diagram, apex `PT_x`, legs `psiInnerLeg U m`. -/
noncomputable def psiInnerCocone (x : X.carrier) (F G : PresheafOfModules.{u} (O X))
    (U : TopologicalSpace.Opens X.carrier) (hxU : x ∈ U) (m : F.obj (Opposite.op U)) :
    Limits.Cocone ((OpenNhds.inclusion x).op ⋙ G.presheaf) where
  pt := AddCommGrpCat.of (grpStalk X ((PresheafOfModules.tensorObj (O := X.presheaf) F G)) x)
  ι :=
    { app := fun j =>
        AddCommGrpCat.ofHom (psiInnerLeg X x F G U hxU m ((OpenNhds.inclusion x).obj j.unop)
            j.unop.2)
      naturality := by
        intro j k g
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro n
        -- `n : G.obj (op Vj)`; the diagram map sends it to `G.obj (op Vk)`.
        set Vj := (OpenNhds.inclusion x).obj j.unop with hVj
        set Vk := (OpenNhds.inclusion x).obj k.unop with hVk
        set gres : (Vk : TopologicalSpace.Opens X.carrier) ⟶ Vj :=
          (OpenNhds.inclusion x).map g.unop with hgres
        change psiInnerLeg X x F G U hxU m Vk k.unop.2
            ((G.presheaf.map gres.op).hom n)
          = psiInnerLeg X x F G U hxU m Vj j.unop.2 n
        change grpGerm X ((PresheafOfModules.tensorObj (O := X.presheaf) F G)) x (U ⊓ Vk) ⟨hxU, k.unop.2⟩
            (((F.restrictₛₗ (homOfLE inf_le_left).op) m)
              ⊗ₜ[X.presheaf.obj (Opposite.op (U ⊓ Vk))]
              ((G.restrictₛₗ (homOfLE inf_le_right).op) ((G.presheaf.map gres.op).hom n)))
          = grpGerm X ((PresheafOfModules.tensorObj (O := X.presheaf) F G)) x (U ⊓ Vj) ⟨hxU, j.unop.2⟩
            (((F.restrictₛₗ (homOfLE inf_le_left).op) m)
              ⊗ₜ[X.presheaf.obj (Opposite.op (U ⊓ Vj))]
              ((G.restrictₛₗ (homOfLE inf_le_right).op) n))
        set i : (U ⊓ Vk : TopologicalSpace.Opens X.carrier) ⟶ (U ⊓ Vj) :=
          homOfLE (inf_le_inf_left U (leOfHom gres)) with hi
        refine Eq.trans ?_ (TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u})
          ((PresheafOfModules.tensorObj (O := X.presheaf) F G)).presheaf i x ⟨hxU, k.unop.2⟩ _)
        congr 1
        change ((F.restrictₛₗ (homOfLE inf_le_left).op) m)
              ⊗ₜ[X.presheaf.obj (Opposite.op (U ⊓ Vk))]
              ((G.restrictₛₗ (homOfLE inf_le_right).op) ((G.presheaf.map gres.op).hom n))
          = ((F).restrictₛₗ i.op ((F.restrictₛₗ (homOfLE inf_le_left).op) m))
              ⊗ₜ[X.presheaf.obj (Opposite.op (U ⊓ Vk))]
              ((G).restrictₛₗ i.op ((G.restrictₛₗ (homOfLE inf_le_right).op) n))
        congr 1
        · change (F.presheaf.map (homOfLE inf_le_left).op).hom m
            = (F.presheaf.map i.op).hom ((F.presheaf.map (homOfLE inf_le_left).op).hom m)
          rw [← CategoryTheory.comp_apply, ← F.presheaf.map_comp]
          congr 2
        · change (G.presheaf.map (homOfLE inf_le_right).op).hom ((G.presheaf.map gres.op).hom n)
            = (G.presheaf.map i.op).hom ((G.presheaf.map (homOfLE inf_le_right).op).hom n)
          rw [← CategoryTheory.comp_apply, ← G.presheaf.map_comp,
            ← CategoryTheory.comp_apply, ← G.presheaf.map_comp]
          congr 2 }

/-- The inner part of the inverse: for `m ∈ F(U)`, the additive map `G_x →+ PT_x`. -/
noncomputable def psiInnerHom (x : X.carrier) (F G : PresheafOfModules.{u} (O X))
    (U : TopologicalSpace.Opens X.carrier) (hxU : x ∈ U) (m : F.obj (Opposite.op U)) :
    grpStalk X G x →+ grpStalk X ((PresheafOfModules.tensorObj (O := X.presheaf) F G)) x :=
  (Limits.colimit.desc _ (psiInnerCocone X x F G U hxU m)).hom

lemma psiInnerHom_germ (x : X.carrier) (F G : PresheafOfModules.{u} (O X))
    (U : TopologicalSpace.Opens X.carrier) (hxU : x ∈ U) (m : F.obj (Opposite.op U))
    (V : TopologicalSpace.Opens X.carrier) (hxV : x ∈ V) (n : G.obj (Opposite.op V)) :
    psiInnerHom X x F G U hxU m (grpGerm X G x V hxV n)
      = grpGerm X ((PresheafOfModules.tensorObj (O := X.presheaf) F G)) x (U ⊓ V) (TopologicalSpace.Opens.mem_inf.mpr ⟨hxU, hxV⟩)
        (((F.restrictₛₗ (homOfLE inf_le_left).op) m)
          ⊗ₜ[X.presheaf.obj (Opposite.op (U ⊓ V))]
          ((G.restrictₛₗ (homOfLE inf_le_right).op) n)) := by
  have h := Limits.colimit.ι_desc (psiInnerCocone X x F G U hxU m)
    (Opposite.op (⟨V, hxV⟩ : OpenNhds x))
  have h2 := congrArg (fun (q : _ ⟶ _) => (ConcreteCategory.hom q) n) h
  exact h2

/-- The outer cocone leg `F(U) →+ (G_x →+ PT_x)`, `m ↦ psiInnerHom U m`. -/
noncomputable def psiOuterLeg (x : X.carrier) (F G : PresheafOfModules.{u} (O X))
    (U : TopologicalSpace.Opens X.carrier) (hxU : x ∈ U) :
    F.obj (Opposite.op U) →+ (grpStalk X G x →+ grpStalk X ((PresheafOfModules.tensorObj (O := X.presheaf) F G)) x) where
  toFun m := psiInnerHom X x F G U hxU m
  map_zero' := by
    apply AddMonoidHom.ext
    intro q
    obtain ⟨V, hxV, n, rfl⟩ :=
      TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u}) (X := X.carrier) G.presheaf q
    change psiInnerHom X x F G U hxU 0 (grpGerm X G x V hxV n) = 0
    rw [psiInnerHom_germ]
    rw [map_zero, TensorProduct.zero_tmul, map_zero]
  map_add' m₁ m₂ := by
    apply AddMonoidHom.ext
    intro q
    obtain ⟨V, hxV, n, rfl⟩ :=
      TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u}) (X := X.carrier) G.presheaf q
    change psiInnerHom X x F G U hxU (m₁ + m₂) (grpGerm X G x V hxV n)
      = psiInnerHom X x F G U hxU m₁ (grpGerm X G x V hxV n)
        + psiInnerHom X x F G U hxU m₂ (grpGerm X G x V hxV n)
    rw [psiInnerHom_germ, psiInnerHom_germ, psiInnerHom_germ]
    rw [map_add, TensorProduct.add_tmul, map_add]

/-- The outer cocone over `F`'s stalk diagram, apex `G_x →+ PT_x`, legs `psiOuterLeg U`. -/
noncomputable def psiOuterCocone (x : X.carrier) (F G : PresheafOfModules.{u} (O X)) :
    Limits.Cocone ((OpenNhds.inclusion x).op ⋙ F.presheaf) where
  pt := AddCommGrpCat.of (grpStalk X G x →+ grpStalk X ((PresheafOfModules.tensorObj (O := X.presheaf) F G)) x)
  ι :=
    { app := fun j =>
        AddCommGrpCat.ofHom (psiOuterLeg X x F G ((OpenNhds.inclusion x).obj j.unop) j.unop.2)
      naturality := by
        intro j k f
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro m
        set Uj := (OpenNhds.inclusion x).obj j.unop with hUj
        set Uk := (OpenNhds.inclusion x).obj k.unop with hUk
        set fres : (Uk : TopologicalSpace.Opens X.carrier) ⟶ Uj :=
          (OpenNhds.inclusion x).map f.unop with hfres
        change psiOuterLeg X x F G Uk k.unop.2 ((F.presheaf.map fres.op).hom m)
          = psiOuterLeg X x F G Uj j.unop.2 m
        -- equality of homs G_x →+ PT_x; check on germs
        apply AddMonoidHom.ext
        intro q
        obtain ⟨V, hxV, n, rfl⟩ :=
          TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u}) (X := X.carrier) G.presheaf q
        change psiInnerHom X x F G Uk k.unop.2 ((F.presheaf.map fres.op).hom m)
            (grpGerm X G x V hxV n)
          = psiInnerHom X x F G Uj j.unop.2 m (grpGerm X G x V hxV n)
        rw [psiInnerHom_germ, psiInnerHom_germ]
        set i : (Uk ⊓ V : TopologicalSpace.Opens X.carrier) ⟶ (Uj ⊓ V) :=
          homOfLE (inf_le_inf_right V (leOfHom fres)) with hi
        refine Eq.trans ?_ (TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u})
          ((PresheafOfModules.tensorObj (O := X.presheaf) F G)).presheaf i x ⟨k.unop.2, hxV⟩ _)
        congr 1
        change ((F.restrictₛₗ (homOfLE inf_le_left).op) ((F.presheaf.map fres.op).hom m))
              ⊗ₜ[X.presheaf.obj (Opposite.op (Uk ⊓ V))]
              ((G.restrictₛₗ (homOfLE inf_le_right).op) n)
          = ((F).restrictₛₗ i.op ((F.restrictₛₗ (homOfLE inf_le_left).op) m))
              ⊗ₜ[X.presheaf.obj (Opposite.op (Uk ⊓ V))]
              ((G).restrictₛₗ i.op ((G.restrictₛₗ (homOfLE inf_le_right).op) n))
        congr 1
        · change (F.presheaf.map (homOfLE inf_le_left).op).hom ((F.presheaf.map fres.op).hom m)
            = (F.presheaf.map i.op).hom ((F.presheaf.map (homOfLE inf_le_left).op).hom m)
          rw [← CategoryTheory.comp_apply, ← F.presheaf.map_comp,
            ← CategoryTheory.comp_apply, ← F.presheaf.map_comp]
          congr 2
        · change (G.presheaf.map (homOfLE inf_le_right).op).hom n
            = (G.presheaf.map i.op).hom ((G.presheaf.map (homOfLE inf_le_right).op).hom n)
          rw [← CategoryTheory.comp_apply, ← G.presheaf.map_comp]
          congr 2 }

/-- The biadditive map `F_x →+ (G_x →+ PT_x)` underlying the inverse `Ψ`. -/
noncomputable def psiBiAdd (x : X.carrier) (F G : PresheafOfModules.{u} (O X)) :
    grpStalk X F x →+ (grpStalk X G x →+ grpStalk X ((PresheafOfModules.tensorObj (O := X.presheaf) F G)) x) :=
  (Limits.colimit.desc _ (psiOuterCocone X x F G)).hom

lemma psiBiAdd_germ (x : X.carrier) (F G : PresheafOfModules.{u} (O X))
    (U : TopologicalSpace.Opens X.carrier) (hxU : x ∈ U) (m : F.obj (Opposite.op U)) :
    psiBiAdd X x F G (grpGerm X F x U hxU m) = psiInnerHom X x F G U hxU m := by
  have h := Limits.colimit.ι_desc (psiOuterCocone X x F G)
    (Opposite.op (⟨U, hxU⟩ : OpenNhds x))
  have h2 := congrArg (fun (q : _ ⟶ _) => (ConcreteCategory.hom q) m) h
  exact h2

/-- Germ formula for `psiBiAdd` on a pure tensor of germs. -/
lemma psiBiAdd_germ_germ (x : X.carrier) (F G : PresheafOfModules.{u} (O X))
    (U : TopologicalSpace.Opens X.carrier) (hxU : x ∈ U) (m : F.obj (Opposite.op U))
    (V : TopologicalSpace.Opens X.carrier) (hxV : x ∈ V) (n : G.obj (Opposite.op V)) :
    psiBiAdd X x F G (grpGerm X F x U hxU m) (grpGerm X G x V hxV n)
      = grpGerm X ((PresheafOfModules.tensorObj (O := X.presheaf) F G)) x (U ⊓ V) (TopologicalSpace.Opens.mem_inf.mpr ⟨hxU, hxV⟩)
        (((F.restrictₛₗ (homOfLE inf_le_left).op) m)
          ⊗ₜ[X.presheaf.obj (Opposite.op (U ⊓ V))]
          ((G.restrictₛₗ (homOfLE inf_le_right).op) n)) := by
  rw [psiBiAdd_germ, psiInnerHom_germ]

/-- The `O_x`-balance condition for `psiBiAdd`, the key fact making `Ψ` well-defined. -/
lemma psiBiAdd_balance (x : X.carrier) (F G : PresheafOfModules.{u} (O X))
    (r : ringStalk X x) (p : grpStalk X F x) (q : grpStalk X G x) :
    psiBiAdd X x F G (r • p) q = psiBiAdd X x F G p (r • q) := by
  -- Choose representatives on a common neighbourhood.
  obtain ⟨Ur, hUr, sr, hsr⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨Um, hUm, sm, hsm⟩ :=
    TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u}) (X := X.carrier) F.presheaf p
  obtain ⟨Un, hUn, sn, hsn⟩ :=
    TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u}) (X := X.carrier) G.presheaf q
  set U : TopologicalSpace.Opens X.carrier := Ur ⊓ Um ⊓ Un with hUdef
  have hxU : x ∈ U := ⟨⟨hUr, hUm⟩, hUn⟩
  set rU : X.presheaf.obj (Opposite.op U) :=
    (X.presheaf.map (homOfLE (le_trans inf_le_left inf_le_left)).op).hom sr with hrU
  set mU : F.obj (Opposite.op U) :=
    (F.map (homOfLE (le_trans inf_le_left inf_le_right)).op).hom sm with hmU
  set nU : G.obj (Opposite.op U) :=
    (G.restrictₛₗ (homOfLE inf_le_right).op) sn with hnU
  have hgr : ringGerm X x U hxU rU = r :=
    (ringGerm_map X x (homOfLE (le_trans inf_le_left inf_le_left)) hxU hUr sr).trans hsr
  have hgm : grpGerm X F x U hxU mU = p :=
    (grpGerm_map X F x (homOfLE (le_trans inf_le_left inf_le_right)) hxU hUm sm).trans hsm
  have hgn : grpGerm X G x U hxU nU = q :=
    (grpGerm_map X G x (homOfLE inf_le_right) hxU hUn sn).trans hsn
  rw [← hgr, ← hgm, ← hgn]
  rw [← stalkModule_germ_smul X F x U hxU rU mU, ← stalkModule_germ_smul X G x U hxU rU nU]
  rw [psiBiAdd_germ_germ, psiBiAdd_germ_germ]
  -- Reduce to a section-level balance on `U ⊓ U`.
  congr 1
  -- `(rU • mU)| ⊗ nU| = mU| ⊗ (rU • nU)|`
  rw [map_smulₛₗ, map_smulₛₗ]
  change ((X.presheaf.map (homOfLE inf_le_left).op).hom rU
        • (F.restrictₛₗ (homOfLE inf_le_left).op) mU)
        ⊗ₜ[X.presheaf.obj (Opposite.op (U ⊓ U))]
        ((G.restrictₛₗ (homOfLE inf_le_right).op) nU)
      = ((F.restrictₛₗ (homOfLE inf_le_left).op) mU)
        ⊗ₜ[X.presheaf.obj (Opposite.op (U ⊓ U))]
        ((X.presheaf.map (homOfLE inf_le_right).op).hom rU
          • (G.restrictₛₗ (homOfLE inf_le_right).op) nU)
  rw [show (X.presheaf.map (homOfLE inf_le_left).op).hom rU
      = (X.presheaf.map (homOfLE inf_le_right).op).hom rU from by
        congr 2]
  rw [TensorProduct.smul_tmul]

/-- **The inverse map `Ψ : F_x ⊗ G_x →+ PT_x`.** -/
noncomputable def psiHom (x : X.carrier) (F G : PresheafOfModules.{u} (O X)) :
    (grpStalk X F x ⊗[ringStalk X x] grpStalk X G x)
      →+ grpStalk X ((PresheafOfModules.tensorObj (O := X.presheaf) F G)) x :=
  TensorProduct.liftAddHom (psiBiAdd X x F G) (psiBiAdd_balance X x F G)

@[simp] lemma psiHom_tmul (x : X.carrier) (F G : PresheafOfModules.{u} (O X))
    (p : grpStalk X F x) (q : grpStalk X G x) :
    psiHom X x F G (p ⊗ₜ[ringStalk X x] q) = psiBiAdd X x F G p q :=
  rfl

/-- Germ formula for `Ψ` on a pure tensor of germs over a common neighbourhood. -/
lemma psiHom_germ_tmul (x : X.carrier) (F G : PresheafOfModules.{u} (O X))
    (U : TopologicalSpace.Opens X.carrier) (hxU : x ∈ U)
    (m : F.obj (Opposite.op U)) (n : G.obj (Opposite.op U)) :
    psiHom X x F G ((grpGerm X F x U hxU m) ⊗ₜ[ringStalk X x] (grpGerm X G x U hxU n))
      = grpGerm X ((PresheafOfModules.tensorObj (O := X.presheaf) F G)) x U hxU
        (m ⊗ₜ[X.presheaf.obj (Opposite.op U)] n) := by
  rw [psiHom_tmul, psiBiAdd_germ_germ]
  -- `germ_{U⊓U}(m| ⊗ n|) = germ_U(m ⊗ n)`
  refine Eq.trans ?_ (TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u})
    ((PresheafOfModules.tensorObj (O := X.presheaf) F G)).presheaf (homOfLE inf_le_left) x ⟨hxU, hxU⟩
    (m ⊗ₜ[X.presheaf.obj (Opposite.op U)] n))
  congr 1

/-- `Ψ ∘ Φ = id`. -/
lemma psiHom_phiHom (x : X.carrier) (F G : PresheafOfModules.{u} (O X))
    (z : grpStalk X ((PresheafOfModules.tensorObj (O := X.presheaf) F G)) x) :
    psiHom X x F G (phiHom X x F G z) = z := by
  obtain ⟨U, hxU, t, rfl⟩ :=
    TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u}) (X := X.carrier)
      ((PresheafOfModules.tensorObj (O := X.presheaf) F G)).presheaf z
  -- `z = germ_U t`; reduce to pure tensors.
  change psiHom X x F G (phiHom X x F G (grpGerm X ((PresheafOfModules.tensorObj (O := X.presheaf) F G)) x U hxU t))
    = grpGerm X ((PresheafOfModules.tensorObj (O := X.presheaf) F G)) x U hxU t
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
  | tmul m n =>
      rw [phiHom_germ]
      exact (congrArg (psiHom X x F G) (phiLeg_tmul X x F G U hxU m n)).trans
        (psiHom_germ_tmul X x F G U hxU m n)

/-- `Φ ∘ Ψ = id`. -/
lemma phiHom_psiHom (x : X.carrier) (F G : PresheafOfModules.{u} (O X))
    (w : grpStalk X F x ⊗[ringStalk X x] grpStalk X G x) :
    phiHom X x F G (psiHom X x F G w) = w := by
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | tmul p q =>
      obtain ⟨Um, hUm, sm, rfl⟩ :=
        TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u}) (X := X.carrier) F.presheaf p
      obtain ⟨Un, hUn, sn, rfl⟩ :=
        TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u}) (X := X.carrier) G.presheaf q
      -- bring to a common neighbourhood
      set U : TopologicalSpace.Opens X.carrier := Um ⊓ Un with hUdef
      have hxU : x ∈ U := ⟨hUm, hUn⟩
      set mU : F.obj (Opposite.op U) := (F.restrictₛₗ (homOfLE inf_le_left).op) sm with hmU
      set nU : G.obj (Opposite.op U) := (G.restrictₛₗ (homOfLE inf_le_right).op) sn with hnU
      have hgm : grpGerm X F x U hxU mU = grpGerm X F x Um hUm sm :=
        grpGerm_map X F x (homOfLE inf_le_left) hxU hUm sm
      have hgn : grpGerm X G x U hxU nU = grpGerm X G x Un hUn sn :=
        grpGerm_map X G x (homOfLE inf_le_right) hxU hUn sn
      change phiHom X x F G (psiHom X x F G
          ((grpGerm X F x Um hUm sm) ⊗ₜ[ringStalk X x] (grpGerm X G x Un hUn sn)))
        = (grpGerm X F x Um hUm sm) ⊗ₜ[ringStalk X x] (grpGerm X G x Un hUn sn)
      rw [← hgm, ← hgn, psiHom_germ_tmul, phiHom_germ, phiLeg_tmul]

/-- `phiLeg` is semilinear over the ring germ: `phiLeg(r • t) = ringGerm r • phiLeg t`. -/
lemma phiLeg_smul (x : X.carrier) (F G : PresheafOfModules.{u} (O X))
    (U : TopologicalSpace.Opens X.carrier) (hxU : x ∈ U)
    (r : X.presheaf.obj (Opposite.op U))
    (t : TensorProduct (X.presheaf.obj (Opposite.op U)) (F.obj (Opposite.op U))
      (G.obj (Opposite.op U))) :
    phiLeg X x F G U hxU (r • t)
      = (ringGerm X x U hxU r) • phiLeg X x F G U hxU t := by
  induction t using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add a b ha hb => rw [smul_add, map_add, map_add, smul_add, ha, hb]
  | tmul m n =>
      rw [TensorProduct.smul_tmul', phiLeg_tmul, phiLeg_tmul]
      rw [stalkModule_germ_smul X F x U hxU r m]
      rw [TensorProduct.smul_tmul']

/-- `Φ` is `O_{X,x}`-linear. -/
lemma phiHom_smul (x : X.carrier) (F G : PresheafOfModules.{u} (O X))
    (r : ringStalk X x) (z : grpStalk X ((PresheafOfModules.tensorObj (O := X.presheaf) F G)) x) :
    phiHom X x F G (r • z) = r • phiHom X x F G z := by
  -- Choose representatives for `r` and `z` on a common neighbourhood.
  obtain ⟨Ur, hUr, sr, hsr⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨Uz, hUz, sz, hsz⟩ :=
    TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u}) (X := X.carrier)
      ((PresheafOfModules.tensorObj (O := X.presheaf) F G)).presheaf z
  set U : TopologicalSpace.Opens X.carrier := Ur ⊓ Uz with hUdef
  have hxU : x ∈ U := ⟨hUr, hUz⟩
  set rU : X.presheaf.obj (Opposite.op U) :=
    (X.presheaf.map (homOfLE inf_le_left).op).hom sr with hrU
  set tU : ((PresheafOfModules.tensorObj (O := X.presheaf) F G)).obj (Opposite.op U) :=
    (((PresheafOfModules.tensorObj (O := X.presheaf) F G)).map (homOfLE inf_le_right).op).hom sz with htU
  have hgr : ringGerm X x U hxU rU = r :=
    (ringGerm_map X x (homOfLE inf_le_left) hxU hUr sr).trans hsr
  have hgz : grpGerm X ((PresheafOfModules.tensorObj (O := X.presheaf) F G)) x U hxU tU = z :=
    (grpGerm_map X _ x (homOfLE inf_le_right) hxU hUz sz).trans hsz
  rw [← hgr, ← hgz]
  rw [← stalkModule_germ_smul X ((PresheafOfModules.tensorObj (O := X.presheaf) F G)) x U hxU rU tU]
  rw [phiHom_germ, phiHom_germ, phiLeg_smul]

end PsiProbe

/-- **(Φ) Tensor product commutes with the filtered colimit defining the stalk.**  The
stalk of the presheaf tensor product `U ↦ F(U) ⊗_{O_X(U)} G(U)` is canonically
`O_{X,x}`-linearly isomorphic to `F_x ⊗_{O_{X,x}} G_x`, sending the germ of a pure tensor
`m ⊗ n` of sections on `U` to `(germ m) ⊗ (germ n)`.

This is the simultaneous "tensor commutes with filtered colimit in the ring and both module
arguments" statement; cf. `TensorProduct.directLimitLeft`/`directLimitRight`. -/
theorem exists_presheafTensorStalkIso (x : X.carrier)
    (F G : SheafOfModules.{u} (structureSheafRing X)) :
    ∃ Φ : (grpStalk X ((PresheafOfModules.tensorObj (O := X.presheaf) F.val G.val)) x) ≃ₗ[ringStalk X x]
        ((grpStalk X F.val x) ⊗[ringStalk X x] (grpStalk X G.val x)),
      ∀ (U : TopologicalSpace.Opens X.carrier) (hxU : x ∈ U)
        (m : F.val.obj (Opposite.op U)) (n : G.val.obj (Opposite.op U)),
        Φ (grpGerm X ((PresheafOfModules.tensorObj (O := X.presheaf) F.val G.val)) x U hxU
            (m ⊗ₜ[X.presheaf.obj (Opposite.op U)] n))
          = (grpGerm X F.val x U hxU m) ⊗ₜ[ringStalk X x] (grpGerm X G.val x U hxU n) := by
  -- SANITY CHECK PASSED
  refine ⟨{
      toFun := phiHom X x F.val G.val
      map_add' := (phiHom X x F.val G.val).map_add
      map_smul' := phiHom_smul X x F.val G.val
      invFun := psiHom X x F.val G.val
      left_inv := psiHom_phiHom X x F.val G.val
      right_inv := phiHom_psiHom X x F.val G.val }, ?_⟩
  intro U hxU m n
  change phiHom X x F.val G.val
      (grpGerm X ((PresheafOfModules.tensorObj (O := X.presheaf) F.val G.val)) x U hxU
        (m ⊗ₜ[X.presheaf.obj (Opposite.op U)] n))
    = (grpGerm X F.val x U hxU m) ⊗ₜ[ringStalk X x] (grpGerm X G.val x U hxU n)
  rw [phiHom_germ, phiLeg_tmul]

/-- **Existence of the canonical isomorphism (Stacks Tag 01CB).**  There is an
`O_{X,x}`-linear isomorphism `(F ⊗_{O_X} G)_x ≃ F_x ⊗_{O_{X,x}} G_x` carrying the germ at
`x` of a local pure tensor `m ⊗ n` of `F ⊗_{O_X} G` to `(germ m) ⊗ (germ n)`.  The
canonical isomorphism `tensorStalkIso` is extracted from this lemma. -/
theorem exists_tensorStalkIso (x : X.carrier)
    (F G : SheafOfModules.{u} (structureSheafRing X)) :
    letI := stalkModule X
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj F).obj G).val x
    ∃ e : (grpStalk X ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj F).obj G)).val x) ≃ₗ[ringStalk X x]
        ((grpStalk X F.val x) ⊗[ringStalk X x] (grpStalk X G.val x)),
      ∀ (U : TopologicalSpace.Opens X.carrier) (hxU : x ∈ U)
        (m : F.val.obj (Opposite.op U)) (n : G.val.obj (Opposite.op U)),
        e (grpGerm X ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj F).obj G)).val x U hxU
            (toTensorSheafSection X F G (Opposite.op U)
              (m ⊗ₜ[X.presheaf.obj (Opposite.op U)] n)))
          = (grpGerm X F.val x U hxU m) ⊗ₜ[ringStalk X x] (grpGerm X G.val x U hxU n) := by
  -- Compose θ : (P^#)_x ≃ P_x  (sheafification preserves stalks)
  -- with     Φ : P_x ≃ F_x ⊗ G_x  (tensor commutes with filtered colimit).
  obtain ⟨θ, hθ⟩ := exists_tensorSheafStalkIso X x F G
  obtain ⟨Φ, hΦ⟩ := exists_presheafTensorStalkIso X x F G
  refine ⟨θ.trans Φ, ?_⟩
  intro U hxU m n
  -- `e = Φ ∘ θ`; `toTensorSheafSection ... t = (sheafifyUnit ...).app _ t`.
  rw [LinearEquiv.trans_apply]
  rw [show toTensorSheafSection X F G (Opposite.op U)
        (m ⊗ₜ[X.presheaf.obj (Opposite.op U)] n)
      = (sheafifyUnit X ((PresheafOfModules.tensorObj (O := X.presheaf) F.val G.val))).app (Opposite.op U)
        (m ⊗ₜ[X.presheaf.obj (Opposite.op U)] n) from rfl]
  rw [hθ U hxU (m ⊗ₜ[X.presheaf.obj (Opposite.op U)] n)]
  rw [hΦ U hxU m n]

/-- **The canonical `O_{X,x}`-linear isomorphism `(F ⊗_{O_X} G)_x ≅ F_x ⊗_{O_{X,x}} G_x`
(Stacks Tag 01CB).**  It is extracted (via `Classical.choice`) from `exists_tensorStalkIso`,
and is characterised on germs of pure tensors by `tensorStalkIso_germ` below. -/
@[stacks 01CB, sga "4 IV 13.5" "ringed spaces"]
noncomputable def tensorStalkIso (x : X.carrier)
    (F G : SheafOfModules.{u} (structureSheafRing X)) :
    letI := stalkModule X
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj F).obj G).val x
    (grpStalk X ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj F).obj G)).val x) ≃ₗ[ringStalk X x]
      ((grpStalk X F.val x) ⊗[ringStalk X x] (grpStalk X G.val x)) :=
  (exists_tensorStalkIso X x F G).choose

/-- **Characterisation of the canonical isomorphism.**  On the germ of a pure tensor of
sections it acts by `germ (m ⊗ n) ↦ (germ m) ⊗ (germ n)`. -/
theorem tensorStalkIso_germ (x : X.carrier)
    (F G : SheafOfModules.{u} (structureSheafRing X))
    (U : TopologicalSpace.Opens X.carrier) (hxU : x ∈ U)
    (m : F.val.obj (Opposite.op U)) (n : G.val.obj (Opposite.op U)) :
    tensorStalkIso X x F G
        (grpGerm X ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj F).obj G)).val x U hxU
          (toTensorSheafSection X F G (Opposite.op U)
            (m ⊗ₜ[X.presheaf.obj (Opposite.op U)] n)))
      = (grpGerm X F.val x U hxU m) ⊗ₜ[ringStalk X x] (grpGerm X G.val x U hxU n) :=
  (exists_tensorStalkIso X x F G).choose_spec U hxU m n

/-- RHS sheafification-unit naturality: the canonical induced sheaf map composed with the
unit equals the unit composed with the presheaf-level induced map. -/
lemma tensorSheafMap_app_toTensorSheafSection
    (F G F' G' : SheafOfModules.{u} (structureSheafRing X))
    (φ : F ⟶ F') (ψ : G ⟶ G')
    (U : TopologicalSpace.Opens X.carrier)
    (m : F.val.obj (Opposite.op U)) (n : G.val.obj (Opposite.op U)) :
    ((((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u}))).map ((φ, ψ) : (_, _) ⟶ (_, _)))).val.app (Opposite.op U)).hom
        (toTensorSheafSection X F G (Opposite.op U)
          (m ⊗ₜ[X.presheaf.obj (Opposite.op U)] n))
      = toTensorSheafSection X F' G' (Opposite.op U)
          ((φ.val.app (Opposite.op U)).hom m ⊗ₜ[X.presheaf.obj (Opposite.op U)]
            (ψ.val.app (Opposite.op U)).hom n) := by
  let sourceTensor := ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj F).obj G
  let targetTensor := ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj F').obj G'
  have tensorMap := Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map
    (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u}) φ ψ
  have sectionMap := congrArg (fun morphism : sourceTensor ⟶ targetTensor =>
    (morphism.val.app (Opposite.op U)).hom
      (toTensorSheafSection X F G (Opposite.op U)
        (m ⊗ₜ[X.presheaf.obj (Opposite.op U)] n))) tensorMap
  have hnat := (PresheafOfModules.sheafificationAdjunction (R := structureSheafRing X)
    (𝟙 (structureSheafRing X).obj)).unit.naturality ((PresheafOfModules.tensorHom (O := X.presheaf) φ.val ψ.val))
  have happ := congrArg (fun α => (PresheafOfModules.Hom.app α (Opposite.op U)).hom
      (m ⊗ₜ[X.presheaf.obj (Opposite.op U)] n)) hnat
  exact sectionMap.trans happ.symm
/-! ### Statement 2: functoriality (naturality) of the isomorphism. -/

/-- **Functoriality of the stalk-of-tensor-product isomorphism (Stacks Tag 01CB).**

Given morphisms `φ : F ⟶ F'` and `ψ : G ⟶ G'` of sheaves of `O_X`-modules, the canonical
isomorphisms `tensorStalkIso` for `(F, G)` and `(F', G')` are natural: the square

```
(F ⊗ G)_x   --tensorStalkIso-->   F_x ⊗ G_x
   |                                   |
(φ⊗ψ)_x                            φ_x ⊗ ψ_x
   v                                   v
(F'⊗ G')_x  --tensorStalkIso-->   F'_x ⊗ G'_x
```

commutes, as a square of `O_{X,x}`-linear maps.  All four maps are the canonical ones:
* the left vertical map is the canonical `O_{X,x}`-linear stalk map (`stalkMapL`) of the
  *canonical* induced morphism `tensorSheafMap φ ψ = φ ⊗ ψ`;
* the right vertical map is `TensorProduct.map φ_x ψ_x`, where `φ_x = stalkMapL φ`,
  `ψ_x = stalkMapL ψ` are the canonical `O_{X,x}`-linear stalk maps of `φ`, `ψ`. -/
theorem tensorStalkIso_natural (x : X.carrier)
    (F G F' G' : SheafOfModules.{u} (structureSheafRing X))
    (φ : F ⟶ F') (ψ : G ⟶ G') :
    letI := stalkModule X
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj F).obj G).val x
    letI := stalkModule X
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj F').obj G').val x
    (TensorProduct.map (stalkMapL X F.val F'.val φ.val x) (stalkMapL X G.val G'.val ψ.val x)).comp
        (tensorStalkIso X x F G).toLinearMap
      = (tensorStalkIso X x F' G').toLinearMap.comp
          (stalkMapL X ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj F).obj G)).val ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj F').obj G')).val
            (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u}))).map ((φ, ψ) : (_, _) ⟶ (_, _)))).val x)  := by
  let tensorPresheaf := PresheafOfModules.tensorObj (O := X.presheaf) F.val G.val
  let sourceTensor := ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj F).obj G
  let targetTensor := ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj F').obj G'
  letI := stalkModule X sourceTensor.val x
  letI := stalkModule X targetTensor.val x
  let tensorMorphism :=
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u}))).map
      ((φ, ψ) : (F, G) ⟶ (F', G'))
  let unitStalk := stalkMapL X tensorPresheaf sourceTensor.val
    (sheafifyUnit X tensorPresheaf) x
  let leftMap := (TensorProduct.map (stalkMapL X F.val F'.val φ.val x)
    (stalkMapL X G.val G'.val ψ.val x)).comp (tensorStalkIso X x F G).toLinearMap
  let rightMap := (tensorStalkIso X x F' G').toLinearMap.comp
    (stalkMapL X sourceTensor.val targetTensor.val tensorMorphism.val x)
  letI := stalkMap_sheafifyUnit_isIso X x tensorPresheaf
  have unitBijective : Function.Bijective unitStalk :=
    ConcreteCategory.bijective_of_isIso (C := AddCommGrpCat.{u})
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf (O X)).map (sheafifyUnit X tensorPresheaf)))
  have onSections (openSet : TopologicalSpace.Opens X.carrier)
      (membership : x ∈ openSet) (sectionValue : tensorPresheaf.obj (.op openSet)) :
      leftMap (grpGerm X sourceTensor.val x openSet membership
          ((sheafifyUnit X tensorPresheaf).app (.op openSet) sectionValue)) =
        rightMap (grpGerm X sourceTensor.val x openSet membership
          ((sheafifyUnit X tensorPresheaf).app (.op openSet) sectionValue)) := by
    let sectionMap : tensorPresheaf.obj (.op openSet) →+ sourceTensor.val.obj (.op openSet) :=
      ((sheafifyUnit X tensorPresheaf).app (.op openSet)).hom.toAddMonoidHom
    let germMap := grpGerm X sourceTensor.val x openSet membership
    let leftEvaluation := leftMap.toAddMonoidHom.comp (germMap.comp sectionMap)
    let rightEvaluation := rightMap.toAddMonoidHom.comp (germMap.comp sectionMap)
    change leftEvaluation sectionValue = rightEvaluation sectionValue
    induction sectionValue using TensorProduct.induction_on with
    | zero => exact (map_zero leftEvaluation).trans (map_zero rightEvaluation).symm
    | add first second firstEquality secondEquality =>
        exact (map_add leftEvaluation first second).trans
          ((congrArg₂ (· + ·) firstEquality secondEquality).trans
            (map_add rightEvaluation first second).symm)
    | tmul leftSection rightSection =>
        have leftEquality := congrArg
          (TensorProduct.map (stalkMapL X F.val F'.val φ.val x)
            (stalkMapL X G.val G'.val ψ.val x))
          (tensorStalkIso_germ X x F G openSet membership leftSection rightSection)
        have mappedTensor := TensorProduct.map_tmul
          (stalkMapL X F.val F'.val φ.val x) (stalkMapL X G.val G'.val ψ.val x)
          (grpGerm X F.val x openSet membership leftSection)
          (grpGerm X G.val x openSet membership rightSection)
        have mappedGerms := congrArg₂
          (fun leftValue rightValue => leftValue ⊗ₜ[ringStalk X x] rightValue)
          (stalkMapL_germ X F.val F'.val φ.val x openSet membership leftSection)
          (stalkMapL_germ X G.val G'.val ψ.val x openSet membership rightSection)
        have rightEquality := congrArg (tensorStalkIso X x F' G')
          (stalkMapL_germ X sourceTensor.val targetTensor.val tensorMorphism.val x
            openSet membership
            (toTensorSheafSection X F G (.op openSet)
              (leftSection ⊗ₜ[X.presheaf.obj (.op openSet)] rightSection)))
        have mappedSection := congrArg
          (fun value => tensorStalkIso X x F' G'
            (grpGerm X targetTensor.val x openSet membership value))
          (tensorSheafMap_app_toTensorSheafSection X F G F' G' φ ψ openSet
            leftSection rightSection)
        exact (leftEquality.trans (mappedTensor.trans mappedGerms)).trans
          ((rightEquality.trans mappedSection).trans
            (tensorStalkIso_germ X x F' G' openSet membership
              ((φ.val.app (.op openSet)).hom leftSection)
              ((ψ.val.app (.op openSet)).hom rightSection))).symm
  have onPresheaf (value : grpStalk X tensorPresheaf x) :
      leftMap (unitStalk value) = rightMap (unitStalk value) := by
    refine (TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u})
      (X := X.carrier) tensorPresheaf.presheaf value).elim fun openSet witness =>
        witness.elim fun membership sectionWitness =>
          sectionWitness.elim fun sectionValue equality => ?_
    have unitGerm := stalkMapL_germ X tensorPresheaf sourceTensor.val
      (sheafifyUnit X tensorPresheaf) x openSet membership sectionValue
    have atGerm := (congrArg leftMap unitGerm).trans
      ((onSections openSet membership sectionValue).trans
        (congrArg rightMap unitGerm).symm)
    exact (congrArg (fun argument => leftMap (unitStalk argument)) equality).symm.trans
      (atGerm.trans (congrArg (fun argument => rightMap (unitStalk argument)) equality))
  apply LinearMap.ext
  intro value
  refine (unitBijective.2 value).elim fun presheafValue equality => ?_
  exact (congrArg leftMap equality).symm.trans
    ((onPresheaf presheafValue).trans (congrArg rightMap equality))

end Stacks.SheafOfModules.TensorStalkRingedSpace
